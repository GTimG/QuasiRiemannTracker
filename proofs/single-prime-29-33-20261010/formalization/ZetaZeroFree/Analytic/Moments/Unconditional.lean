import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence
import ZetaZeroFree.Analytic.Moments.Exceptional

set_option maxRecDepth 16384
set_option maxHeartbeats 0


/- From OAI.NumberTheory.DirichletL.Moments.PrimeGlobal. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical ContDiff

open Set

namespace SevenEighths.CenteredMomentPrimeGlobal

open OAI.SevenEighths.CenteredMomentPrimeGlobal hiding ray_prime_global_squared

open HeckeFamily HeckePrimeRay HeckeZeroSupremum

lemma zeroMaximum_le_one {ι : Type*} [Fintype ι]
    (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum χ hχ T ≤ 1 :=
  (HeckeDetectorZeros.zeroMaximum_bounds χ hχ T).2

variable (M : Ideal O) [NeZero M]

local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem ray_prime_global_squared (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e slack η σmin σmax κ : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hslack : 0<slack) (hη : 0≤η)
    (hbudget : 8*e*R+slack≤ε) 
    (hκ : 1 ≤ κ) :
    ∃ C : ℝ,0<C ∧ ∀ Z d : ℝ,1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (χ : Character) (_hn : ∀θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (i : ℕ),
    ∀ r σ freq : ℝ,0≤r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      (∀θ : RayQuotient.Characters M H,
        (twistedFamily M H hH χ θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq‖^2≤
        C*(Z^d)^(κ*r+2*ε) := by
  obtain ⟨C,hC,hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    R dmax τ ε e slack η σmin σmax hR hdmax hτ hε he he' hslack hη hbudget
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro Z d hZ hd hdmax hU hT χ hn i r σ freq hr hrR hσ hσmax hlarge hQ hf ht
  have hmax := zeroMaximum_le_one (twistedFamily M H hH χ) hn
    (3*(i+1:ℕ)*Z^τ)
  have hb := hbound Z d hZ hd hdmax hU hT χ hn 1 i (by norm_num) le_rfl
    (by linarith) r σ freq hr hrR hσ hσmax hlarge hQ hf ht
  have hUp : 0<Z^d := by linarith
  have hp : ((Z^d)^(((1:ℝ)-1/2)*r+ε))^2 = (Z^d)^(2*(((1:ℝ)-1/2)*r+ε)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  calc
    _≤(C*(Z^d)^(((1:ℝ)-1/2)*r+ε))^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _=C^2*(Z^d)^(2*(((1:ℝ)-1/2)*r+ε)) := by rw [mul_pow,hp]
    _≤C^2*(Z^d)^(κ*r+2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Z^d)
        (by nlinarith [mul_le_mul_of_nonneg_right hκ hr])) (sq_nonneg _)

end SevenEighths.CenteredMomentPrimeGlobal

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.PrimeHeight. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators ContDiff

open Set

namespace SevenEighths.CenteredMomentPrimeHeight

open OAI.SevenEighths.CenteredMomentPrimeHeight hiding ray_prime_all_height_large ray_prime_all_height_squared

open HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDyadic HeckeZeroSupremum

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem ray_prime_all_height_large (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (_hLs : 0≤Lslot) (hloss : 0<loss)
     (hκ : 1 ≤ κ) :
    ∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧ ∀ Z P : ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀χ : Character,(χ.modulus.absNorm:ℝ)≤Z^Lmod →
      (∀θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).residue≠1) →
    ∀σ freq : ℝ,lo≤σ → σ≤hi →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log P →
      ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C*P^κ*Z^loss*(3+|freq|)^loss := by
  let d := max Lmod Lslot+2
  have hd : 0<d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hd1 : 1≤d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hmd : Lmod+1≤d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hsd : Lslot≤d := by dsimp [d];have := le_max_right Lmod Lslot;linarith
  let eps := loss/(2*d)
  have heps : 0<eps := by dsimp [eps];positivity
  let e := min (eps/32) (1/2000)
  have he : 0<e := lt_min (by positivity) (by norm_num)
  have he' : e<1/1000 := (min_le_right _ _).trans_lt (by norm_num)
  have hbudget : 8*e*1+eps/2≤eps := by have := min_le_left (eps/32) (1/2000);dsimp [e];linarith
  obtain ⟨C,hC,hbound⟩ := ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentPrimeGlobal.ray_prime_global_squared M H hH W A B hA hWs hW
    1 d 1 eps e (eps/2) (4/d) lo hi κ (by norm_num) hd.le (by norm_num) heps he he'
    (by positivity) (by positivity) hbudget  hκ
  let Z₀ := max 2 (M.absNorm:ℝ)
  refine ⟨C,Z₀,hC,lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_left _ _),?_⟩
  intro Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi hlarge
  have hz2 : 2≤Z := (le_max_left _ _).trans hZ
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hMZ : (M.absNorm:ℝ)≤Z := (le_max_right _ _).trans hZ
  let T := 3+|freq|
  let Zt := Z*T
  let U := Zt^d
  have hT3 : 3≤T := by dsimp [T];linarith [abs_nonneg freq]
  have hT : 0<T := by linarith
  have hzt6 : 6≤Zt := by dsimp [Zt];nlinarith
  have hzt : 0<Zt := by linarith
  have hzt1 : 1≤Zt := by linarith
  have hZzt : Z≤Zt := by dsimp [Zt];nlinarith
  have hTzt : T≤Zt := by dsimp [Zt];nlinarith
  have hztU : Zt≤U := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hzt1 hd1
  have hU : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hPU : P≤U := hPcap.trans ((Real.rpow_le_rpow_of_exponent_le hz1 hsd).trans
    (Real.rpow_le_rpow hz.le hZzt hd.le))
  let r := Real.logb U P
  have hr : 0≤r := Real.logb_nonneg hU hP
  have hr1 : r≤1 := (Real.logb_le_iff_le_rpow hU (zero_lt_one.trans_le hP)).mpr
    (by simpa only [Real.rpow_one] using hPU)
  have hPr : U^r=P := Real.rpow_logb hUp (ne_of_gt hU) (zero_lt_one.trans_le hP)
  have hQ (θ : RayQuotient.Characters M H) : ((twistedFamily M H hH χ θ).modulus.absNorm:ℝ)≤U := by
    have ht : ((twistedFamily M H hH χ θ).modulus.absNorm:ℝ)≤(χ.modulus.absNorm:ℝ)*M.absNorm := by
      exact_mod_cast HeckePrimeScale.twisted_modulus_bound M H hH χ θ
    apply ht.trans
    calc
      _ ≤ Z^Lmod*Z := mul_le_mul hχ hMZ (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
      _ = Z^(Lmod+1) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ Z^d := Real.rpow_le_rpow_of_exponent_le hz1 hmd
      _ ≤ U := Real.rpow_le_rpow hz.le hZzt hd.le
  have hheight : (3+2*Zt)^2≤U^(4/d) := by
    have heq : U^(4/d)=Zt^(4:ℝ) := by
      dsimp [U]
      rw [←Real.rpow_mul hzt.le]
      congr 1
      field_simp
    rw [heq,Real.rpow_ofNat]
    have hb : 3+2*Zt≤Zt^2 := by nlinarith
    calc
      _ ≤ (Zt^2)^2 := pow_le_pow_left₀ (by positivity) hb 2
      _ = _ := by ring
  have hb := hbound Zt d hzt1 hd.le le_rfl (by linarith : 2≤Zt^d)
    (by simpa only [Real.rpow_one] using (show (2:ℝ)<Zt by linarith)) χ hn 0 r σ freq hr hr1 hσ hσhi
    (by change _≤Real.log (U^r);rw [hPr];exact hlarge) hQ
    (by norm_num only [Nat.mul_zero,Nat.zero_add,Nat.cast_ofNat,Real.rpow_one];dsimp [T] at hTzt;linarith)
    (by simpa only [Nat.mul_zero,Nat.zero_add,Nat.cast_ofNat,Real.rpow_one] using hheight)
  change ‖rayPrimePolynomial M H χ W B (U^r) σ freq‖^2≤C*U^(κ*r+2*eps) at hb
  rw [hPr] at hb
  apply hb.trans_eq
  dsimp only [U,Zt,r,eps,T]
  rw [lifted_scale_power Z (3+|freq|) d P κ loss hz hT hd.ne' hU (zero_lt_one.trans_le hP)]
  ring

theorem ray_prime_all_height_squared (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
     (hκ : 1 ≤ κ) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧ ∀ Z P : ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀χ : Character,(χ.modulus.absNorm:ℝ)≤Z^Lmod →
      (∀θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).residue≠1) →
    ∀σ freq : ℝ,lo≤σ → σ≤hi →
      ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C*(1+|freq|)^degree*Z^loss*P^κ := by
  obtain ⟨Cbig,Z₀,hCbig,hZ₀,hbig⟩ := ray_prime_all_height_large M H hH W A B hA hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss  hκ
  let K := 2*(|Real.log A|+|Real.log B|)+1
  have hK : 0≤K := by dsimp [K];positivity
  obtain ⟨Csmall,hCs,hsmall⟩ := ray_prime_bounded_scale M H W A B lo hi (Real.exp K) hA hWs hW.continuous
    (Real.one_le_exp hK)
  let degree := ⌈loss⌉₊
  let C0 := Cbig+Csmall^2
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0*(3:ℝ)^degree,Z₀,by positivity,hZ₀,?_⟩
  intro Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi
  have hz1 : 1≤Z := hZ₀.le.trans hZ
  have hκ0 : 0≤κ := by linarith
  have hpκ : 1≤P^κ := Real.one_le_rpow hP hκ0
  have hzloss : 1≤Z^loss := Real.one_le_rpow hz1 hloss.le
  have htbase : 1≤3+|freq| := by linarith [abs_nonneg freq]
  have htloss : 1≤(3+|freq|)^loss := Real.one_le_rpow htbase hloss.le
  have hbase : ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C0*P^κ*Z^loss*(3+|freq|)^loss := by
    by_cases hlarge : K≤Real.log P
    · exact (hbig Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi hlarge).trans
        (by dsimp [C0];gcongr; nlinarith [sq_nonneg Csmall])
    · have hPD : P≤Real.exp K := by
        have he := Real.exp_le_exp.mpr (le_of_not_ge hlarge)
        simpa only [Real.exp_log (zero_lt_one.trans_le hP)] using he
      have hb := pow_le_pow_left₀ (norm_nonneg _) (hsmall χ P σ freq hP hPD hσ hσhi) 2
      apply hb.trans
      calc
        Csmall^2 ≤ C0 := by dsimp [C0];linarith
        _ ≤ C0*P^κ := le_mul_of_one_le_right hC0.le hpκ
        _ ≤ C0*P^κ*Z^loss := le_mul_of_one_le_right (by positivity) hzloss
        _ ≤ _ := le_mul_of_one_le_right (by positivity) htloss
  have hheight : (3+|freq|)^loss≤(3:ℝ)^degree*(1+|freq|)^degree := by
    calc
      _ ≤ (3+|freq|)^(degree:ℝ) := Real.rpow_le_rpow_of_exponent_le htbase (Nat.le_ceil loss)
      _ = (3+|freq|)^degree := Real.rpow_natCast _ _
      _ ≤ (3*(1+|freq|))^degree := pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg freq]) _
      _ = _ := mul_pow _ _ _
  apply hbase.trans
  calc
    _ ≤ C0*P^κ*Z^loss*((3:ℝ)^degree*(1+|freq|)^degree) :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentPrimeHeight

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators ContDiff Topology

open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_relative_slot_bound

open HeckeFamily HeckeRowClosure HeckePrimeRay HeckeZeroSupremum

open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource

open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge

open CenteredMomentFixedRayInducingTransport CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

theorem natural_relative_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
     (hκ : 1 ≤ κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff η₀.inverse I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W a b ha hWs hW (Lmod+1) Lslot loss lo hi κ (by linarith) hLs hloss  hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  filter_upwards [eventually_ge_atTop Z₀,eventually_ge_atTop (η₀.modulus.absNorm:ℝ),
    eventually_gt_atTop (0:ℝ)] with Z hZ0 hη₀ hZ
  intro P hP hPcap η z hz F hcond Q hQM hex σ t v hσ hσhi
  have hc : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤Z^(Lmod+1) := by
    have hb : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤
        (F.character.modulus.absNorm:ℝ)*(η₀.modulus.absNorm:ℝ) := by
      exact_mod_cast HeckePrimeScale.product_modulus_bound F.character η₀.inverse
    apply hb.trans
    calc
      _≤Z^Lmod*Z := mul_le_mul hcond hη₀ (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
      _=Z^(Lmod+1) := by rw [Real.rpow_add hZ,Real.rpow_one]
  have hb:=hbound Z P hZ0 hP hPcap (F.character.product η₀.inverse) hc
    (natural_relative_twists M H hH F hz η₀ Q hQM hex) σ (t+v) hσ hσhi
  rw [relative_normalizedSlot_eq_ray M H η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W b P σ t v (zero_lt_one.trans_le hP),norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) degree

theorem natural_character_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
     (hκ : 1 ≤ κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ν : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → Q≤ν.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_relative_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss  hκ
  refine ⟨degree,C,hC,?_⟩
  intro ν
  filter_upwards [hbound ν.inverse] with Z hz
  intro P hP hPcap η z hz0 F hcond Q hQM hQν hex σ t v hσ hσhi
  have hQeq : internalQ Q ν.inverse=Q := inf_eq_left.mpr hQν
  have he:=hz P hP hPcap η z hz0 F hcond Q hQM (by simpa only [hQeq] using hex) σ t v hσ hσhi
  simpa only [idealCoeff_inverse_conj,starRingEnd_self_apply] using he

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceRayPrime. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators ContDiff Topology

open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalRowSource

open CenteredExceptionalProfile CenteredMomentSecondHeightFamily

open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_ray_slots_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
     (hκ : 1 ≤ κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀θ : RayQuotient.Characters M H,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
          HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_character_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss  hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  have hall:=Filter.eventually_all.mpr (fun θ : RayQuotient.Characters M H=>
    hbound (relativeCharacter M H hH η₀ θ))
  filter_upwards [hall] with Z hz
  intro θ P hP hPcap η z hz0 F hcond Q hQM hex σ t v hσ hσhi
  exact hz θ P hP hPcap η z hz0 F hcond (internalQ Q η₀)
    (inf_le_left.trans hQM)
    (relativeCharacter_fixedQ M H hH η₀ θ (internalQ Q η₀) (inf_le_left.trans hQM) inf_le_right)
    hex σ t v hσ hσhi

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSlots. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators ContDiff

open Filter

namespace SevenEighths.CenteredMomentRayMaskedFloor

open OAI.SevenEighths.CenteredMomentRayMaskedFloor hiding natural_slot_product

open HeckeFamily HeckeZeroSupremum ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion

open CenteredMomentCommonMaskEnergy CenteredMomentWholeSlotDeletion

open CenteredMomentHeckeSlots CenteredMomentPrimeSlot CenteredExceptionalProfile

open CenteredMomentSecondHeightFamily

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_slot_product {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
     (hκ : 1 ≤ κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(z : O),z≠0 → ∀N : NaturalRow η z,
      (N.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
    ∀A : Finset α,A⊆F →
      ‖∏i∈A,naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      C*(1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  let el : ℝ := loss/(F.card+1)
  have hel : 0<el := div_pos hloss (by positivity)
  obtain ⟨J,C,hC,hbound⟩ := natural_ray_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot el lo hi κ hLm hLs hel  hκ
  let C₀ := max 1 C
  have hC₀ : 1≤C₀ := le_max_left _ _
  refine ⟨J*F.card,C₀^F.card,pow_pos (zero_lt_one.trans_le hC₀) _,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η z hz0 N hmod Q hQM hex A hAF
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hk : 0≤κ := by linarith
  have hh : 1≤1+|t|+T := by linarith [abs_nonneg t]
  have hslot (i : α) (hi : i∈A) :
      ‖naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      (C₀*(1+|t|+T)^J)*Z^(el+κ*w i) := by
    rw [natural_slot_eq N]
    have he := hz (θ i) (Z^(w i)) (Real.one_le_rpow hZ.le (hw i (hAF hi)))
      (Real.rpow_le_rpow_of_exponent_le hZ.le (hwL i (hAF hi))) η z hz0 N hmod Q hQM hex
      (σ i) t (v i) (hσlo i (hAF hi)) (hσhi i (hAF hi))
    apply he.trans
    rw [←Real.rpow_mul hZ0.le]
    calc
      _ ≤ (C₀*(1+|t|+T)^J)*Z^el*Z^(w i*κ) := by
        gcongr
        · exact le_max_right 1 C
        · exact hv i (hAF hi)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hZ0]; congr 2 ; ring
  rw [norm_prod,←Finset.prod_pow]
  apply (Finset.prod_le_prod₀ (fun i _=>sq_nonneg _) hslot).trans
  rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hZ0]
  have hexp : (∑i∈A,(el+κ*w i))≤loss+κ*(∑i∈F,w i) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum]
    have hc : (A.card:ℝ)≤F.card+1 := by exact_mod_cast (Finset.card_le_card hAF).trans (Nat.le_succ _)
    have he : (A.card:ℝ)*el≤loss := by
      calc
        _ ≤ (F.card+1)*el := mul_le_mul_of_nonneg_right hc hel.le
        _ = _ := by dsimp [el]; field_simp
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hAF (fun i hi _=>hw i hi)
    nlinarith
  have hp : 1≤C₀*(1+|t|+T)^J := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hh)
  apply (mul_le_mul (pow_le_pow_right₀ hp (Finset.card_le_card hAF))
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) (by positivity) (by positivity)).trans_eq
  rw [mul_pow,←pow_mul]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorNatural. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentRayMaskedFloor

open OAI.SevenEighths.CenteredMomentRayMaskedFloor hiding natural_pair_slots natural_slot_product

open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy

open CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot

open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison

open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile

open CenteredMomentRadialEligibleEnergy (Radial)

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_pair_slots {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
     (hκ : 1 ≤ κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ),Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ → ∀A : Finset α,A⊆F →
      radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
        ∏i∈A,naturalSlot (naturalCharacter η z) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
        r.keep r.profile r.scale ≤
      C*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  obtain ⟨J,Cs,hCs,hslot⟩ := natural_slot_product M H hH F W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss  hκ
  obtain ⟨S,Cp,hCp,hplain⟩ := global_positive_scale a₀ b₀ ha₀
  refine ⟨J,S,Cp^4*3^8*Cs,by positivity,?_⟩
  intro η₀
  filter_upwards [hslot η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ A hAF
  let E := Cs*(1+|t|+T)^J*Z^(loss+κ*(∑i∈F,w i))
  have hE : 0≤E := by dsimp [E]; positivity
  let B₁ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁ : 0≤B₁ := apply_nonneg _ _
  have hB₂ : 0≤B₂ := apply_nonneg _ _
  let B := Cp^2*(B₁*B₂)*Qbound^2*3^4*Real.sqrt E
  have hB : 0≤B := by dsimp [B]; positivity
  have hpoint (z : O) (hkeep : r.keep z) :
      ‖polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
        ∏i∈A,naturalSlot (naturalCharacter η z) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖≤B := by
    have hn := hz z hkeep
    have heq := naturalCharacter_eq η z hn
    have hnon : (naturalCharacter η z).residue≠1 := by
      rw [heq]
      exact CenteredMomentNonprincipalGate.actual_row_nonprincipal η
        (naturalRow η z hn).character (internalQ Q η₀) fixedBadMask 1 z
        (by simpa only [one_mul] using (naturalRow η z hn).element) (hex z hkeep)
    have h₁ : ‖polynomial (naturalCharacter η z) false W₁ X₁ 0 0‖≤Cp*B₁*Qbound*3^2 := by
      have he := hplain W₁ hs₁ _ hnon X₁ 0 hX₁
      norm_num only [abs_zero,add_zero] at he
      apply he.trans
      simpa only [show (3:ℝ)^2=9 by norm_num] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hQ z hkeep) (mul_nonneg hCp.le hB₁)) (show (0:ℝ)≤9 by norm_num))
    have h₂ : ‖polynomial (naturalCharacter η z) false W₂ X₂ 0 0‖≤Cp*B₂*Qbound*3^2 := by
      have he := hplain W₂ hs₂ _ hnon X₂ 0 hX₂
      norm_num only [abs_zero,add_zero] at he
      apply he.trans
      simpa only [show (3:ℝ)^2=9 by norm_num] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hQ z hkeep) (mul_nonneg hCp.le hB₂)) (show (0:ℝ)≤9 by norm_num))
    have hs := hZ θ w σ v t T hw hwL hσlo hσhi hT hv η z hn (naturalRow η z hn)
      (by simpa only [heq] using hmod z hkeep) Q hQM (hex z hkeep) A hAF
    rw [←heq] at hs
    have hsroot := (Real.le_sqrt (norm_nonneg _) hE).mpr hs
    rw [norm_mul,norm_mul]
    apply (mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity))
      hsroot (norm_nonneg _) (by positivity)).trans_eq
    dsimp [B,B₁,B₂]
    norm_num only [abs_zero,add_zero]
    ring
  have he := radial_bound_on_keep _ r B hB hpoint
  apply he.trans_eq
  dsimp [B,E,B₁,B₂]
  rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hE]
  ring

end SevenEighths.CenteredMomentRayMaskedFloor

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorShared. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentRayMaskedFloor

open OAI.SevenEighths.CenteredMomentRayMaskedFloor hiding masked_natural_pair_slots natural_pair_slots natural_slot_product

open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy

open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot

open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison

open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile

open CenteredMomentRadialEligibleEnergy (Radial)

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem masked_natural_pair_slots {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
     (hκ : 1 ≤ κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ)(R : Ideal O),R≠0 → Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false W₁ X₁ 0 0*
        polynomial (excluded (naturalCharacter η z) R) false W₂ X₂ 0 0*
        ∏i∈F,naturalSlot (excluded (naturalCharacter η z) R) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
        r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := natural_pair_slots M H hH F W a b ha hWs hW a₀ b₀ ha₀
    Lmod Lslot loss lo hi κ hLm hLs hloss  hκ
  obtain ⟨B,hB,hcoeff⟩ := slot_coefficient_bounds W a b lo hi ha hWs hW.continuous
  obtain ⟨Cd,hCd,hdelete⟩ := CenteredMomentCommonMaskRadialEnergy.actual_radial_shared_energy
    F (fun _=>b) (fun _=>B) (fun _ _=>hB.le) ε hε
  refine ⟨J,S,Cd*C,mul_pos hCd hC,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound R hR hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  let E := C*diagonalControl r.profile*max 1 r.scale*
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
      (1+|t|+T)^J*Z^(loss+κ*(∑i∈F,w i))
  have hd := diagonalControl_nonneg r.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hp (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈primePool M H b (Z^(w i))) : Prime I :=
    (Finset.mem_filter.mp hI).2.1
  have hc (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈primePool M H b (Z^(w i))) :=
    hcoeff (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (v i) t
      (Real.rpow_pos_of_pos hZ0 _) (hσlo i hi) (hσhi i hi) I (hp i hi I hI).ne_zero
  have he := hdelete (CompletedGauss.primeSupport R) (support_prime R) (naturalCharacter η)
    W₁ W₂ X₁ X₂ a₀ b₀ a₀ b₀ (fun i=>primePool M H b (Z^(w i)))
    (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t)
    (fun i=>Z^(w i)) r.keep r.profile r.scale E hX₁ hX₂ hb₀ hb₀ hs₁ hs₂ hp
    (fun _ _=>Real.rpow_pos_of_pos hZ0 _) (fun i hi I hI=>(hc i hi I hI).1)
    (fun i hi I hI=>(hc i hi I hI).2) r.scale_pos r.nonneg hE ?_
  · rw [primeSupport_product_radical R hR] at he
    exact he.trans_eq (by dsimp [E]; ring)
  · intro D₁ hD₁ D₂ hD₂ A hA
    have hn (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport R).powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime R I (Finset.mem_powerset.mp hD hi)).ne_zero)))
    exact hZ θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound hQM hQbound hz hex hmod hQ
      W₁ W₂ hs₁ hs₂ _ _ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂))
      (F\A) Finset.sdiff_subset

end SevenEighths.CenteredMomentRayMaskedFloor

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSource. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentRayMaskedFloor

open OAI.SevenEighths.CenteredMomentRayMaskedFloor hiding masked_natural_pair_slots natural_pair_slots natural_slot_product original_masked_positive_floor

open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy

open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot

open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison

open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile

open CenteredMomentRadialEligibleEnergy (Radial)

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem original_masked_positive_floor {α : Type*} [Fintype α] [DecidableEq α] (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
     (hκ : 1 ≤ κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤T → (∀i,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ)(R : Ideal O),R≠0 → Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      CenteredMomentInductionEnergy.energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t
        W₁ W₂ (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := masked_natural_pair_slots M H hH (Finset.univ : Finset α)
    W a b ha hWs hW a₀ b₀ ε ha₀ hb₀ hε Lmod Lslot loss lo hi κ hLm hLs hloss  hκ
  obtain ⟨n,T₀,Ct,hCt,ht⟩ :=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a₀ b₀ ha₀ S
  refine ⟨4*n+J,T₀,C*Ct^4,by positivity,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound R hR hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hexbase (z : O) (hk : r.keep z) :
      ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z := by
    intro hh
    apply hex z hk
    exact (CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff η (internalQ Q η₀)
      fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
      (ConcretePrimeRowBridge.idealGenerator_ne_zero R hR) one_ne_zero (hz z hk)
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hh
  let V₁ := CenteredMomentLattice.normPowerProfile W₁ a₀ b₀ ha₀ hs₁ (W₁.smooth ⊤) t
  let V₂ := CenteredMomentLattice.normPowerProfile W₂ a₀ b₀ ha₀ hs₂ (W₂.smooth ⊤) t
  have hv₁ : Function.support (V₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ :=
    (CenteredMomentTwist.normPowerProfile_support W₁ a₀ b₀ ha₀ hs₁ (W₁.smooth ⊤) t).trans hs₁
  have hv₂ : Function.support (V₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ :=
    (CenteredMomentTwist.normPowerProfile_support W₂ a₀ b₀ ha₀ hs₂ (W₂.smooth ⊤) t).trans hs₂
  have he := hZ θ w σ v t T (fun i _=>hw i) (fun i _=>hwL i)
    (fun i _=>hσlo i) (fun i _=>hσhi i) hT (fun i _=>hv i)
    η Q r Qbound R hR hQM hQbound hz hexbase hmod hQ V₁ V₂ hv₁ hv₂ X₁ X₂ hX₁ hX₂
  have hid : CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale =
    radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false V₁ X₁ 0 0*
      polynomial (excluded (naturalCharacter η z) R) false V₂ X₂ 0 0*
      ∏i,naturalSlot (excluded (naturalCharacter η z) R) (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
      r.keep r.profile r.scale := by
    unfold CenteredMomentInductionEnergy.energy radialEnergy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · simp only [hk,ite_true]
      rw [original_positive_normalized (naturalRow η z (hz z hk)) R hR W₁ W₂
        a₀ b₀ a₀ b₀ ha₀ ha₀ hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
        _ _ _ (fun i=>Real.rpow_pos_of_pos hZ0 _) t X₁ X₂ hX₁ hX₂]
      rw [norm_mul,norm_mul,positive_height_phase_norm X₁ t hX₁,
        positive_height_phase_norm X₂ t hX₂,one_mul,one_mul,naturalCharacter_eq η z (hz z hk)]
    · simp only [hk,ite_false]
  rw [hid]
  apply he.trans
  have hB₁ := ht W₁ hs₁ t
  have hB₂ := ht W₂ hs₂ t
  have hprod : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₁ *
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₂)^2 ≤
      (Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+|t|+T)^(4*n) := by
    have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_le_mul hB₁ hB₂ (apply_nonneg _ _) (by positivity)) 2
    have hheight : (1+‖t‖)^(4*n)≤(1+|t|+T)^(4*n) := by
      apply pow_le_pow_left₀ (by positivity)
      rw [Real.norm_eq_abs]
      linarith
    calc
      _ ≤ (Ct*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*(1+‖t‖)^n*
        (Ct*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)*(1+‖t‖)^n))^2 := hh
      _ = (Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n) := by
          rw [Nat.mul_comm 4 n,pow_mul]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hheight (by positivity)
  have hd := diagonalControl_nonneg r.profile
  calc
    _ ≤ C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
      ((Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+|t|+T)^(4*n))*Qbound^4*
      (1+|t|+T)^J*Z^(loss+κ*(∑i,w i)) := by gcongr
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentRayMaskedFloor

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.RayMaskedFloor. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentRayMaskedFloor

open OAI.SevenEighths.CenteredMomentRayMaskedFloor hiding masked_natural_pair_slots natural_masked_positive_floor natural_pair_slots natural_slot_product original_masked_positive_floor

open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy

open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot

open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison

open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile

open CenteredMomentRadialEligibleEnergy (Radial)

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_masked_positive_floor {α : Type*} [Fintype α] [DecidableEq α] (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (L Lslot loss lo hi κ bΦ : ℝ) (hL : 0≤L) (hbΦ : 0≤bΦ) (hLs : 0≤Lslot) (hloss : 0<loss)
     (hκ : 1 ≤ κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤T → (∀i,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(R : Ideal O),R≠0 → Q≤M →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
    ∀(m q ρ : ℝ),0≤m → 0≤q → m+q≤ρ → ρ≤L → r.scale=Z^m →
      (η.modulus.absNorm:ℝ)≤Z^q →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      CenteredMomentInductionEnergy.energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t
        W₁ W₂ (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*bΦ^4*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*
         (1+|t|+T)^degree*Z^(m+4*ρ+loss+κ*(∑i,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := original_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ ε ha₀ hb₀ hε (L+1) Lslot loss lo hi κ (by linarith) hLs hloss  hκ
  let Fc : ℝ := fixedConductorFactor
  have hFc : 0<Fc := by
    unfold Fc fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨J,S,C*Fc^4,by positivity,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_ge_atTop (Fc*bΦ),eventually_ge_atTop (1:ℝ)] with Z hZ hconst hZ1
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r R hR hQM hz hex hsΦ
    m q ρ hm hq hρ hρL hscale hη W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ1
  let r' : Radial := {r with keep := fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  have hmod (z : O) (hk : r'.keep z) :
      ((naturalCharacter η z).modulus.absNorm:ℝ)≤Fc*bΦ*Z^ρ := by
    have hn := hz z hk.1
    rw [naturalCharacter_eq η z hn]
    have hrow : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m := by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←hscale]
      exact (div_le_iff₀ r.scale_pos).mp (hsΦ hk.2)
    have he := (naturalRow η z hn).modulus_power_bound Z q m bΦ hZ0 hbΦ hη hrow
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hFc.le hbΦ)
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hcap (z : O) (hk : r'.keep z) :
      ((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^(L+1) := by
    apply (hmod z hk).trans
    calc
      _ ≤ Z*Z^L := mul_le_mul hconst (Real.rpow_le_rpow_of_exponent_le hZ1 hρL)
        (Real.rpow_nonneg hZ0.le _) hZ0.le
      _ = _ := by rw [Real.rpow_add hZ0,Real.rpow_one]; ring
  have he := hZ θ w σ v t T hw hwL hσlo hσhi hT hv η Q r'
    (Fc*bΦ*Z^ρ) R hR hQM (by positivity) (fun z hk=>hz z hk.1)
    (fun z hk=>hex z hk.1) hcap hmod W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hid : CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r'.keep r'.profile r'.scale =
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale := by
    unfold CenteredMomentInductionEnergy.energy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · by_cases hp : r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · simp [r',hk,hp]
    · simp [r',hk]
  rw [hid] at he
  dsimp only [r'] at he
  rw [hscale,max_eq_right (Real.one_le_rpow hZ1 hm)] at he
  rw [hscale]
  apply he.trans_eq
  have hzpow : Z^m*(Z^ρ)^4*Z^(loss+κ*(∑i,w i))=Z^(m+4*ρ+loss+κ*(∑i,w i)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ0.le,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    norm_num
    ring
  calc
    _ = (C*Fc^4*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*bΦ^4*
      ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*
      (1+|t|+T)^J)*(Z^m*(Z^ρ)^4*Z^(loss+κ*(∑i,w i))) := by ring
    _ = _ := by rw [hzpow]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorState. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentRayMaskedFloor

open OAI.SevenEighths.CenteredMomentRayMaskedFloor hiding exists_positive_floor masked_natural_pair_slots natural_masked_positive_floor natural_pair_slots natural_slot_product original_masked_positive_floor

open HeckeFamily HeckeZeroSupremum QuadraticInitialBound

open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentPrimeSlot CenteredMomentInductionEnergy

local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem exists_positive_floor {α : Type*} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ bΦ Bmask ε Lslot lo hi κ : ℝ)
    (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hbΦ : 0<bΦ) (hmask : 0≤Bmask)
    (hε : 0<ε) (hLs : 0≤Lslot)  (hκ : 1 ≤ κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤T → (∀i,|v i|≤T) →
    ∀(Q : Ideal O),Q≤M → ∀s : NaturalState Z Bmask bΦ,
      s.fixedModulus=internalQ Q η₀ → s.width≤ε/16 → 6*κ*(∑i,w i)≤s.width →
    ∀p : Profiles a₀ b₀,∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^degree*Z^(s.width+ε) := by
  let e : ℝ := ε/(4*(Bmask+1))
  have he : 0<e := div_pos hε (by positivity)
  have hcost : Bmask*e≤ε/4 := by
    have hh := mul_le_mul_of_nonneg_left (show Bmask≤Bmask+1 by linarith) he.le
    have hid : e*(Bmask+1)=ε/4 := by dsimp [e]; field_simp
    rw [hid] at hh
    linarith
  obtain ⟨J,S,C,hC,hfloor⟩ := natural_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ e ha₀ hb₀ he (ε/16) Lslot (ε/4) lo hi κ bΦ (by positivity) hbΦ.le hLs
    (by positivity)  hκ
  refine ⟨J,S,C*bΦ^4,mul_pos hC (pow_pos hbΦ _),?_⟩
  intro η₀
  filter_upwards [hfloor η₀] with Z hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hZ1 := s.base_ge_one
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ1
  have hrad : (s.puncture.radical.absNorm:ℝ)^e≤Z^(Bmask*e) := by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hex (z : O) (hz : s.radial.keep z) :
      ¬CenteredExceptionalProfile.FixedInducingRow s.character (internalQ Q η₀)
        (fixedBadMask*ConcretePrimeRowBridge.idealGenerator s.puncture) 1 z := by
    rw [←hQ]
    exact s.nonexceptional z hz
  have hh := hZ θ w σ v t T hw hwL hσlo hσhi hT hv s.character Q s.radial s.puncture
    s.puncture_ne_zero hQM s.row_ne_zero hex s.radial_support s.rowWidth s.characterWidth
    (ε/16) s.row_nonneg s.character_nonneg hs le_rfl s.scale_eq s.modulus_bound
    (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) X₁ X₂ hX₁ hX₂
  have hwidth : s.rowWidth≤s.width := by dsimp [NaturalState.width]; linarith [s.character_nonneg]
  have hbudget : Bmask*e+(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤s.width+ε := by
    linarith
  have hpow : Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤Z^(s.width+ε) := by
    rw [←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 hbudget
  have hd := diagonalControl_nonneg s.radial.profile
  have hc := p.control_nonneg S
  apply hh.trans
  change C*(s.puncture.radical.absNorm:ℝ)^e*diagonalControl s.radial.profile*bΦ^4*
    (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤_
  calc
    _ ≤ C*Z^(Bmask*e)*diagonalControl s.radial.profile*bΦ^4*
      (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i)) := by gcongr
    _ = (C*bΦ^4*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^J)*
      (Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.Bands. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open HeckeFamily CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentPrimeSlot QuadraticInitialBound

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem exists_positive_bottom (W:ℝ→ℂ)(aslot bslot:ℝ)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (a b bΦ Bmask L Lslot lo hi ε κ:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hmask:0≤Bmask)(hε:0<ε)(hLs:0≤Lslot)
    (hκ:1 ≤ κ):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀η₀:Character,∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Q:Ideal O,Q≤M→
        PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
          (ε/16) ε κ Z η₀ Q degree S C:=by
  have hs (T:Finset α):=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentRayMaskedFloor.exists_positive_floor (α:=T)
    M H hH W aslot bslot haslot hWs hW a b bΦ Bmask ε Lslot lo hi κ
    ha hb hbΦ hmask hε hLs  hκ
  choose J S C hC hbound using hs
  let S₀:Finset (ℕ×ℕ):=Finset.univ.biUnion S
  let C₀:ℝ:=1+∑T:Finset α,C T
  have hC₀:0<C₀:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hC T).le)
    dsimp [C₀];linarith
  refine ⟨∑T:Finset α,J T,S₀,C₀,hC₀,?_⟩
  intro η₀
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr (fun T=>hbound T η₀)
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Q hQM T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hslots:6*κ*(∑i,w i)≤s.width:=by
    linarith [length_nonneg Z X₁ hZ1,length_nonneg Z X₂ hZ1]
  have hh:=hZ T θ w σ v t height hw hwL hσlo hσhi hheight hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hsub:S T⊆S₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hpc:p.control (S T)≤p.control S₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hc:C T≤C₀:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hC T).le)
      (Finset.mem_univ T)
    dsimp [C₀];linarith
  have hj:J T≤∑T:Finset α,J T:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hpow:(1+|t|+height)^(J T)≤(1+|t|+height)^(∑T:Finset α,J T):=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hj
  have hd:=diagonalControl_nonneg s.radial.profile
  have hp:=p.control_nonneg S₀
  have hpt:=p.control_nonneg (S T)
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyBands

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.RelativeCapacityRemoval. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators ContDiff Topology

namespace SevenEighths.CenteredMomentRelativeCapacityRemoval

open OAI.SevenEighths.CenteredMomentRelativeCapacityRemoval hiding actual_relative_capacity_removal relative_slots_uniform

open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile

open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular

open CenteredMomentNaturalRowSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_relative_slot_bound

open CenteredMomentSecondHeightFamily Filter

local notation "O"=>HeckeFamily.O

variable (M:Ideal O)[NeZero M]

local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

include hH

theorem relative_slots_uniform {ι:Type*}[Fintype ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ)(hLm:0≤Lmod)(hLs:0≤Lslot)(hloss:0<loss)
    (hκ:1 ≤ κ):
    ∃degree:ℕ,∃C:ℝ,1≤C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → Q≤(ν i).modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀σ t v V:ℝ,lo≤σ → σ≤hi → 0≤V → |v|≤V →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) P)
        (fun I=>idealCoeff (ν i) I*annularWeight (W i) P σ v I) t P‖^2≤
        C*(1+|t|+V)^degree*Z^loss*P^κ := by
  choose degree C hC hb using fun i=>natural_character_slot_bound M H hH (W i) (a i) (b i)
    (ha i) (hWs i) (hW i) Lmod Lslot loss lo hi κ hLm hLs hloss  hκ
  let Ctotal:ℝ:=1+∑i,C i
  have hCtotal:1≤Ctotal:=by
    have hsum:=Finset.sum_nonneg (fun i (_:i∈Finset.univ)=>(hC i).le)
    dsimp [Ctotal];linarith
  have hCi (i:ι):C i≤Ctotal:=by
    have hsum:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp [Ctotal];linarith
  refine ⟨∑i,degree i,Ctotal,hCtotal,?_⟩
  intro ν
  have hev:∀ᶠZ:ℝ in atTop,∀i:ι,_ := Filter.eventually_all.mpr (fun i=>hb i (ν i))
  obtain ⟨Zbase,hbase⟩:=eventually_atTop.mp hev
  refine ⟨max 2 Zbase,lt_max_of_lt_left (by norm_num),?_⟩
  intro i Z P hZ hP hPcap η z hz F hcond Q hQM hQν hex σ t v V hσ hσhi hV hv
  have hZ0:Zbase≤Z:=(le_max_right _ _).trans hZ
  have hZp:0<Z:=lt_of_lt_of_le (by norm_num:0<(2:ℝ)) ((le_max_left _ _).trans hZ)
  refine (hbase Z hZ0 i P hP hPcap η z hz F hcond Q hQM hQν hex σ t v hσ hσhi).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
  apply mul_le_mul (hCi i) _ (by positivity) (zero_le_one.trans hCtotal)
  calc
    _≤(1+|t|+V)^(degree i):=pow_le_pow_left₀ (by positivity) (by linarith) _
    _≤_:=pow_le_pow_right₀ (by linarith [abs_nonneg t])
      (Finset.single_le_sum (fun j _=>Nat.zero_le _) (Finset.mem_univ i))

theorem actual_relative_capacity_removal {ι:Type*}[Fintype ι][DecidableEq ι]
    (W:ι→ℝ→ℂ)(a b:ι→ℝ)(ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i))(hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot ε lo hi κ:ℝ)(hLm:0≤Lmod)(hLs:0≤Lslot)(hε:0<ε)
    (hκ:1 ≤ κ):
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤OAI.SevenEighths.CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q:Ideal O,Q≤M → (∀i,Q≤(ν i).modulus) → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*annularWeight (W i) (P i) (σ i) (freq i) I
      ‖selectedProduct J η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+OAI.SevenEighths.CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          ‖selectedProduct (J\R) η fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂‖^2 := by
  let N:=Fintype.card ι
  let loss:=ε/((N:ℝ)+1)
  have hloss:0<loss:=div_pos hε (by positivity)
  obtain ⟨degree,C,hC,hbound⟩:=relative_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss  hκ
  have hκpos:0<κ:=by linarith
  refine ⟨degree*N,C^N,pow_pos (zero_lt_one.trans_le hC) _,?_⟩
  intro ν
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound ν
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  let excess:=OAI.SevenEighths.CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ
  obtain ⟨R,hR,hRsum,hpay,hcost⟩:=whole_removal J w excess κ mesh (le_max_right _ _) hκpos hmesh
    (fun i _=>hw i) (fun i _=>hwm i)
  refine ⟨R,hR,OAI.SevenEighths.CenteredMomentLiveCapacity.remaining_capacity J R hR w n₁ n₂ width κ hpay,hcost,?_⟩
  intro Z hZ η z hz F hcond Q hQM hQν hex σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
  dsimp only
  have hZ1:1≤Z:=hZ₀.le.trans hZ
  have hZp:0<Z:=zero_lt_one.trans_le hZ1
  let B:=C*(1+|t|+V)^degree*Z^loss
  have hB:1≤B:=by
    have ht:1≤(1+|t|+V)^degree:=one_le_pow₀ (by linarith [abs_nonneg t])
    have hz:1≤Z^loss:=Real.one_le_rpow hZ1 hloss.le
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC ht) hz
  have hs:∀i∈R,‖normalizedSlot η fixedBadMask 1 z (primePool M H (b i) (Z^(w i)))
      (fun I=>idealCoeff (ν i) I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I) t (Z^(w i))‖^2≤
      B*Z^(κ*w i) := by
    intro i hi
    have hb:=hbound i Z (Z^(w i)) hZ (Real.one_le_rpow hZ1 (hw i))
      (Real.rpow_le_rpow_of_exponent_le hZ1 (hwcap i)) η z hz F hcond Q hQM (hQν i) hex
      (σ i) t (freq i) V (hσ i) (hσhi i) hV (hfreq i)
    rw [←Real.rpow_mul hZp.le] at hb
    simpa only [B,mul_comm (w i) κ] using hb
  have he:=selectedProduct_energy_remove J R hR η fixedBadMask 1 z W₁ W₂
    (fun i=>primePool M H (b i) (Z^(w i)))
    (fun i I=>idealCoeff (ν i) I*annularWeight (W i) (Z^(w i)) (σ i) (freq i) I)
    (fun i=>Z^(w i)) t X₁ X₂ Z κ hZp w (fun _=>B) (fun i hi=>zero_le_one.trans hB) hs
  apply he.trans
  gcongr 1
  have hcard:R.card≤N:=Finset.card_le_univ R
  have hpow:(∏i∈R,B)≤B^N:=by
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ hB hcard
  have hcostZ:Z^(κ*∑i∈R,w i)≤Z^(excess/6+κ*mesh):=
    Real.rpow_le_rpow_of_exponent_le hZ1 hcost
  have hsplit:B^N=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)):=by
    dsimp [B]
    rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_natCast (Z^loss) N,←Real.rpow_mul hZp.le]
  have hlossN:loss*(N:ℝ)≤ε:=by
    dsimp [loss]
    have hden:0<(N:ℝ)+1:=by positivity
    have hh:ε/((N:ℝ)+1)*((N:ℝ)+1)=ε:=div_mul_cancel₀ _ hden.ne'
    nlinarith [hloss.le]
  calc
    _≤B^N*Z^(excess/6+κ*mesh):=mul_le_mul hpow hcostZ (Real.rpow_nonneg hZp.le _) (by positivity)
    _=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)+(excess/6+κ*mesh)):=by
      rw [hsplit,mul_assoc,←Real.rpow_add hZp]
    _≤_:=mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)) (by positivity)
  apply le_of_eq
  congr 3
  ext i
  simp

end SevenEighths.CenteredMomentRelativeCapacityRemoval

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CapacityRemoval. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyCapacityRemoval

open OAI.SevenEighths.CenteredMomentEnergyCapacityRemoval hiding actual_relative_state_capacity_removal actual_state_capacity_removal

open HeckeFamily ConcreteTraceCRT CenteredMomentRetainedEnergy

open CenteredMomentInductionEnergy CenteredMomentWholeSlotDeletion

open CenteredMomentPrimeSlot

open CenteredMomentSlotNormalization ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentRelativeCapacityRemoval

open OAI.SevenEighths.CenteredMomentRelativeCapacityRemoval hiding actual_relative_capacity_removal relative_slots_uniform

open CenteredMomentNaturalRowSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_relative_slot_bound

open CenteredMomentSecondHeightFamily CenteredMomentEnergyState

open CenteredExceptionalProfile CenteredMomentFixedRowMask

local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (M : Ideal O) [NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

theorem actual_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0<a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi κ : ℝ) (hbΦ : 0≤bΦ)
    (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hε : 0<ε)
     (hκ : 1 ≤ κ) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤OAI.SevenEighths.CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.puncture=1 → s.rowWidth≤Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤Z^q → Mrow+q+1≤Lmod →
    ∀Q:Ideal O,s.fixedModulus=Q → Q≤M → (∀i,Q≤(ν i).modulus) →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0<X₁ → 0<X₂ →
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
        (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+OAI.SevenEighths.CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
            (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_relative_capacity_removal M H hH W a b ha hWs hW
    Lmod Lslot ε lo hi κ hLm hLs hε  hκ
  obtain ⟨Zsupport,hsupport⟩:=eventually_atTop.mp (eventual_row_conductor bΦ Mrow hbΦ)
  refine ⟨degree,C,hC,?_⟩
  intro ν
  obtain ⟨Zbase,hZbase,hbound⟩:=hbound ν
  refine ⟨max Zbase Zsupport,lt_of_lt_of_le hZbase (le_max_left _ _),?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hcapacity,hcost,hpoint⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hcapacity,hcost,?_⟩
  intro Z hZ Bmask s hpuncture hrow q hmod hLmod Q hQ hQM hQν σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂ hX₁ hX₂
  dsimp only
  have hZbase' : Zbase≤Z:=(le_max_left _ _).trans hZ
  have hs:=(hsupport Z ((le_max_right _ _).trans hZ))
  have hZpos:0<Z:=zero_lt_one.trans hs.1
  have hscale (i:ι) : 0≤Z^(w i):=Real.rpow_nonneg hZpos.le _
  let P:=fun i=>Z^(w i)
  let S:=fun i=>primePool M H (b i) (P i)
  let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
  let cost:=C*(1+|t|+V)^degree*Z^(ε+OAI.SevenEighths.CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)
  have hmask:s.mask=fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1:=by rw [NaturalState.mask,hpuncture]
  rw [hmask,unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero,
    unit_puncture_energy _ _ _ _ _ _ _ _ _ _ s.row_ne_zero]
  change energy s.character fixedBadMask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
    (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
    cost*energy s.character fixedBadMask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
    (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale
  have hsum (T:Finset ι):=compact_radial_summable
    (fun z=>positiveSlotRow s.character fixedBadMask 1 z W₁ W₂ (fun i:T=>S i)
      (fun i:T=>coeff i) (fun i:T=>P i) t X₁ X₂)
    s.radial.keep s.radial.profile s.radial.scale bΦ s.radial.scale_pos s.radial_support
  unfold energy
  rw [←tsum_mul_left]
  apply (hsum J).tsum_le_tsum _ ((hsum (J\R)).mul_left cost)
  intro z
  by_cases hk:s.radial.keep z
  · simp only [ite_eq_left hk]
    by_cases hp:s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)=0
    · simp [hp]
    · have hz:=s.row_ne_zero z hk
      have hc:((naturalRow s.character z hz).character.modulus.absNorm:ℝ)≤Z^Lmod:=
        (hs.2 Bmask s hrow q hmod z hz hp).trans
          (Real.rpow_le_rpow_of_exponent_le hs.1.le hLmod)
      have hh:=hpoint Z hZbase' s.character z hz (naturalRow s.character z hz) hc
        Q hQM hQν (state_unit_nonexceptional s hpuncture Q hQ z hk)
        σ freq t V hσ hσhi hV hfreq W₁ W₂ X₁ X₂
      dsimp only at hh
      rw [selected_eq_positive J s.character fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂ (mul_pos hX₁ hX₂).le hscale,
        selected_eq_positive (J\R) s.character fixedBadMask 1 z W₁ W₂ S coeff P t X₁ X₂ (mul_pos hX₁ hX₂).le hscale] at hh
      exact (mul_le_mul_of_nonneg_right hh (s.radial.nonneg z)).trans_eq (by dsimp only [cost];ring)
  · simp only [ite_eq_right hk,mul_zero,le_refl]

theorem actual_relative_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0<a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi κ : ℝ) (hbΦ : 0≤bΦ)
    (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hε : 0<ε)
     (hκ : 1 ≤ κ) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀η₀:Character,∀θ:ι→RayQuotient.Characters M H,
    let ν:=fun i=>relativeCharacter M H hH η₀ (θ i);
    ∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤OAI.SevenEighths.CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.puncture=1 → s.rowWidth≤Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤Z^q → Mrow+q+1≤Lmod →
    ∀Q:Ideal O,s.fixedModulus=internalQ Q η₀ → Q≤M →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0<X₁ → 0<X₂ →
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
        (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+OAI.SevenEighths.CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
            (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  obtain ⟨degree,C,hC,hbound⟩:=actual_state_capacity_removal M H hH W a b ha hWs hW
    Mrow bΦ Lmod Lslot ε lo hi κ hbΦ hLm hLs hε  hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀ θ
  dsimp only
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound (fun i=>relativeCharacter M H hH η₀ (θ i))
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hcapacity,hcost,henergy⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hcapacity,hcost,?_⟩
  intro Z hZ Bmask s hpuncture hrow q hmod hLmod Q hQ hQM
  exact henergy Z hZ Bmask s hpuncture hrow q hmod hLmod (internalQ Q η₀) hQ
    (inf_le_left.trans hQM)
    (fun i=>relativeCharacter_fixedQ M H hH η₀ (θ i) (internalQ Q η₀)
      (inf_le_left.trans hQM) inf_le_right)

end SevenEighths.CenteredMomentEnergyCapacityRemoval

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.PaidRemoval. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyPaidRemoval

open OAI.SevenEighths.CenteredMomentEnergyPaidRemoval hiding actual_paid_bands

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open OAI.SevenEighths.CenteredMomentEnergyPaidBands ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCapacityRemoval

open OAI.SevenEighths.CenteredMomentEnergyPaidBands

open OAI.SevenEighths.CenteredMomentEnergyCapacityRemoval hiding actual_relative_state_capacity_removal actual_state_capacity_removal

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

local notation "O" => HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(Q:Ideal O),Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(J:Finset α)(w σ v:α→ℝ)(t height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|v i|≤height) →
    ∀s:NaturalState Z Bmask bΦ,s.puncture=1 → s.fixedModulus=internalQ Q η₀ → s.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i:J=>primePool M H bslot (Z^(w i)))
      (fun (i:J) I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i:J=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      Cc*(C₀+C₁)*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^(dc+degree)*
        Z^(s.width+εchild+εremove+
          OAI.SevenEighths.CenteredMomentLiveCapacity.excess J w (length Z X₁) (length Z X₂) s.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hrem⟩:=actual_relative_state_capacity_removal (ι:=α) M H hH
    (fun _=>W) (fun _=>aslot) (fun _=>bslot) (fun _=>ha) (fun _=>hWs) (fun _=>hW)
    Mcap bΦ (2*Mcap+1) Lslot εremove lo hi κ hbΦ (by linarith) hLs hε  hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hrem⟩:=hrem η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    J w σ v t height mesh hmesh hw hwm hwL hσlo hσhi hheight hv s hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  obtain ⟨R,hR,hcapacity,hcost,henergy⟩:=hrem J w (length Z X₁) (length Z X₂)
    s.width mesh hmesh hw hwm hwL
  have hrow:s.rowWidth≤Mcap:=by
    have hc:=s.character_nonneg
    dsimp [NaturalState.width] at hs
    linarith
  have hq:Mcap+s.characterWidth+1≤2*Mcap+1:=by
    have hr:=s.row_nonneg
    dsimp [NaturalState.width] at hs
    linarith
  have he:=henergy Z hZ Bmask s hunit hrow s.characterWidth s.modulus_bound hq Q hQ hQM
    σ v t height hσlo hσhi hheight hv (p.profile 0) (p.profile 1) X₁ X₂ hX₁ hX₂
  dsimp only at he
  have hb:=remaining_energy_bound M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap εchild κ Z
    η₀ Q degree S C₀ C₁ hC₀ hC₁ hzero hpos J R θ w σ v t height
    hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  apply he.trans ((mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq ?_)
  simp only [pow_add,Real.rpow_add hZp]
  ring

end SevenEighths.CenteredMomentEnergyPaidRemoval

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.AllocatedPaid. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedPaid

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyPaidRemoval CenteredMomentInductionEnergy

open OAI.SevenEighths.CenteredMomentEnergyPaidRemoval hiding actual_paid_bands

open CenteredMomentFiniteProfileExceptional ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope

open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

local notation "O" => HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_allocated_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(Q:Ideal O),Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) a b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁ → 0<X₂ → X₁≤Z^L → X₂≤Z^L →
    let d:=commonData (withHeight src st.character v) C R B
    energy st.character st.mask 1 0 (p.profile 0) (p.profile 1)
      (fun i:remaining src C B D alloc J=>d.slots i.val)
      (fun i:remaining src C B D alloc J=>CenteredMomentCommonMaskEnergy.heightCoefficient (d.coefficient i.val) v)
      (fun i:remaining src C B D alloc J=>d.P i.val)
      X₁ X₂ st.radial.keep st.radial.profile st.radial.scale ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*(p.control S)^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          OAI.SevenEighths.CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z X₁) (length Z X₂) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε  hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  dsimp only
  rw [common_energy hmatch st.character v C R B D alloc J st.mask 1
    (p.profile 0) (p.profile 1) X₁ X₂ st.radial.keep st.radial.profile st.radial.scale]
  have he:=hbound Z hZ a b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    (originalImage src C B D alloc J) w σ (fun i=>v+freq i) 0 (|v|+height) mesh
    hmesh hw hwm hwL hσlo hσhi (add_nonneg (abs_nonneg _) hheight)
    (fun i=>(abs_add_le _ _).trans (add_le_add le_rfl (hfreq i)))
    st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂
  simpa only [abs_zero,add_zero] using he

end SevenEighths.CenteredMomentEnergyAllocatedPaid

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.AllocatedClipped. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedClipped

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_clipped_paid_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(a b Bmask L εchild:ℝ)(ha:0<a),0≤L → ∀Q:Ideal O,Q≤M →
    ∀(degree:ℕ)(S:Finset (ℕ×ℕ))(C₀ C₁:ℝ),0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src st.character v) C R B
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b ha (p.profile 0) (p.support 0))
      (sourcePlain a b ha (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        ((pair D alloc ha p v X₁ X₂ hX₁ hX₂).control S)^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          OAI.SevenEighths.CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_allocated_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε  hκ
  refine ⟨dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ a b Bmask L εchild ha hL Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  rw [allocated_pair st hunit]
  exact hbound Z hZ (a/max 1 b) b Bmask L εchild Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs (pair D alloc ha p v X₁ X₂ hX₁ hX₂)
    (scale D alloc X₁ 0 F₁) (scale D alloc X₂ 1 F₂)
    (scale_pos D alloc X₁ 0 F₁ hF₁) (scale_pos D alloc X₂ 1 F₂ hF₂)
    (scale_cap D alloc Z L X₁ st.base_ge_one hL hX₁ hc₁ 0 F₁ hF₁)
    (scale_cap D alloc Z L X₂ st.base_ge_one hL hX₂ hc₂ 1 F₂ hF₂)

end SevenEighths.CenteredMomentEnergyAllocatedClipped

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.AllocatedHomogeneous. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_clipped_homogeneous_bands (W:ℝ→ℂ)(aslot bslot Mcap bΦ Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hbΦ:0≤bΦ)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀(Bmask εchild:ℝ)(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀st:NaturalState Z Bmask bΦ,st.puncture=1 → st.fixedModulus=internalQ Q η₀ → st.width≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src st.character v) C R B
    allocatedEnergy st.character st.radial D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(st.width+εchild+εremove+
          OAI.SevenEighths.CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh) := by
  obtain ⟨dc,Cc,hCc,hbound⟩:=actual_clipped_paid_bands (α:=α) M H hH W aslot bslot Mcap bΦ Lslot
    εremove lo hi κ ha hWs hW hMcap hbΦ hLs hε  hκ
  obtain ⟨n,T,Cp,hCp,hprofile⟩:=retained_pair_control a b haPlain S
  refine ⟨n,T,dc,Cc*Cp^2,mul_pos hCc (sq_pos_of_pos hCp),?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ Bmask εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have he:=hbound Z hZ a b Bmask L εchild haPlain hL Q hQM degree S C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st hunit hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only at he ⊢
  let U:Fin 2→ℝ:=![rawScale D alloc X₁ 0,rawScale D alloc X₂ 1]
  have hU:∀i,0<U i:=by
    intro i;fin_cases i
    · exact rawScale_pos D alloc X₁ hX₁ 0
    · exact rawScale_pos D alloc X₂ hX₂ 1
  have hp:(pair D alloc haPlain p v X₁ X₂ hX₁ hX₂).control S≤
      Cp*p.control T*(1+|v|+height)^(2*n):=by
    have h:=hprofile p U hU v
    have hpw:(1+‖v‖)^(2*n)≤(1+|v|+height)^(2*n):=
      pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs];linarith) _
    exact h.trans (mul_le_mul_of_nonneg_left hpw (mul_nonneg hCp.le (p.control_nonneg T)))
  apply he.trans
  calc
    _≤Cc*(C₀+C₁)*diagonalControl st.radial.profile*
        (Cp*p.control T*(1+|v|+height)^(2*n))^2*
        (1+(|v|+height))^(dc+degree)*
        Z^(st.width+εchild+εremove+
          OAI.SevenEighths.CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh):=by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans st.base_ge_one) _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2)
        (mul_nonneg (mul_nonneg hCc.le (add_nonneg hC₀ hC₁)) (diagonalControl_nonneg _))
    _=_:=by
      have hpow:(1+|v|+height)^(4*n)=((1+|v|+height)^(2*n))^2:=by
        rw [←pow_mul]
        congr 1
        omega
      simp only [←add_assoc,mul_pow,pow_add,hpow]
      ring

end SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Moments.FirstMixedRoot. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMixedRoot

open OAI.SevenEighths.CenteredMomentFirstMixedRoot hiding active_span_swap

open CanonicalQuadraticSieve OAI.SevenEighths.CenteredMomentFirstMixedAllowance

open OAI.SevenEighths.CenteredMomentFirstMixedAllowance

open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstNonexceptionalPrefactor

open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon

open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily

open CenteredMomentFirstScale CenteredMomentSupportedCorrelation

local notation "O"=>HeckeFamily.O

lemma active_span_swap (C D:Ideal O):
    Ideal.span {activeConductor D C}=Ideal.span {activeConductor C D}:=by
  rw [activeConductor_span_filter,activeConductor_span_filter,
    CenteredMomentCompleteCommon.commonSupport_comm D C]
  congr 1
  apply Finset.filter_congr
  intro P hP
  simp only [CenteredMomentActive.netExponent]
  omega

open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData

open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

open HeckeFamily CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentFirstMixedRoot

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalChildBound. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalChildBound

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_canonical_child_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        ((τ.modulus.absNorm:ℝ)*CenteredMomentSectorLocalization.dyadicScale (dyad 1))*
        Z^(εchild+εremove+
          OAI.SevenEighths.CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
            (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) (Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)) κ/6+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_clipped_homogeneous_bands (α:=α) M H hH W aslot bslot
    Mcap 2 Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap (by norm_num)
    hLs hε  hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have hZ1:1<Z:=hZ₀.trans_le hZ
  let st:=canonicalState Z 0 hZ1 τ (internalQ Q η₀) 1 one_ne_zero (by simp) dyad hn
  have he:=hbound Z hZ 0 εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J st rfl rfl hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  have hpow:=canonicalState_power Z 0 hZ1 τ (internalQ Q η₀) 1 one_ne_zero (by simp) dyad hn
  change Z^st.width=(τ.modulus.absNorm:ℝ)*CenteredMomentSectorLocalization.dyadicScale (dyad 1) at hpow
  dsimp only at he ⊢
  have heq:st.width+εchild+εremove+
      OAI.SevenEighths.CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
        (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh =
    st.width+(εchild+εremove+OAI.SevenEighths.CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
      (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂)) st.width κ/6+κ*mesh):=by ring
  rw [heq,Real.rpow_add (zero_lt_one.trans hZ1),hpow] at he
  convert he using 1 <;> simp only [st,canonicalState,NaturalState.width] ; ring

end SevenEighths.CenteredMomentEnergyCanonicalChildBound

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalLiveBound. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLiveBound

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_live_canonical_child_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    ∀Mnom cost:ℝ,
    (LiveChild τ (canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J →
      Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom+
        OAI.SevenEighths.CenteredMomentLiveCapacity.excess (originalImage src C B D alloc J) w
          (length Z (scale D alloc X₁ 0 F₁)) (length Z (scale D alloc X₂ 1 F₂))
          (Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)) κ/6≤cost) →
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+cost+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_canonical_child_bands (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε  hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  intro Mnom cost hcost
  have hz:1<Z:=hZ₀.trans_le hZ
  have hz0:0<Z:=zero_lt_one.trans hz
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  by_cases hne:LiveChild τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J
  · have he:=hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
    dsimp only at he
    have hnorm:0<(τ.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
    have hpower:Z^(Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ))=
        (τ.modulus.absNorm:ℝ)*dyadicScale (dyad 1):=by
      rw [Real.rpow_add hz0,Real.rpow_logb hz0 hz.ne' (dyadicScale_pos _),
        Real.rpow_logb hz0 hz.ne' hnorm,mul_comm]
    apply he.trans
    rw [←hpower,mul_assoc,←Real.rpow_add hz0]
    apply mul_le_mul_of_nonneg_left _ (by
      have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
      have hp:=p.control_nonneg T
      positivity)
    apply Real.rpow_le_rpow_of_exponent_le hz.le
    have hh:=hcost hne
    linarith
  · have he:=energy_zero_of_not_live τ rad (fun z hz=>hz.1) D alloc V₁ V₂
      d.slots d.coefficient d.P d.P_pos v X₁ X₂ hX₁ hX₂ F₁ F₂ J hF₁ hF₂ hne
    change allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
      v X₁ X₂ hX₁ hX₂ F₁ F₂ J≤_
    rw [he]
    have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
    have hp:=p.control_nonneg T
    positivity

end SevenEighths.CenteredMomentEnergyCanonicalLiveBound

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalPaidSource. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalPaidSource

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_canonical_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b:ℝ)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
      (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)),
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0<X₁,∀hX₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
    ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
    let d:=commonData (withHeight src τ v) C R B
    ∀A Mparent Mnom u ell δ₁ δ₂ θclip:ℝ,
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (X₁*X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-Mparent+6*(u+ell)+δ₁ →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    allocatedEnergy τ (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad) D alloc
      (sourcePlain a b haPlain (p.profile 0) (p.support 0))
      (sourcePlain a b haPlain (p.profile 1) (p.support 1))
      d.slots d.coefficient d.P v X₁ X₂ hX₁ hX₂ F₁ F₂ J ≤
      Cc*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_live_canonical_child_bands (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε  hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
  dsimp only
  intro A Mparent Mnom u ell δ₁ δ₂ θclip hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  apply hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
    Mnom (δ₂+u+ell+δ₁/6+θclip/3)
  intro hlive
  exact live_source_paid_cost src C R B D alloc J τ (canonicalRadial τ (internalQ Q η₀) dyad)
    (sourcePlain a b haPlain (p.profile 0) (p.support 0))
    (sourcePlain a b haPlain (p.profile 1) (p.support 1))
    v Z X₁ X₂ κ A Mparent Mnom
    (Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ))
    u ell δ₁ δ₂ θclip w hX₁ hX₂ F₁ F₂ (hZ₀.trans_le hZ)
    (by linarith) hw hmatch.scale hF₁ hF₂ hparent hshift hdefect hu hell hδ₁ hδ₂ hθclip hclip hlive

end SevenEighths.CenteredMomentEnergyCanonicalPaidSource

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalCommonPaid. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_common_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent Mnom u ell δ₁ δ₂ θclip:ℝ,
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Mnom≤
      A-Mparent+6*(u+ell)+δ₁ →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Mnom≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_canonical_paid_source (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b haPlain L hL degree S ha hWs hW hMcap hLs hε  hκ
  obtain ⟨Cm,hCm,hcommon⟩:=actual_common_from_energy (α:=α) (fun _=>bslot) (fun _=>Mslot)
    (fun _=>hMslot) εmask hεmask
  refine ⟨n,T,dc,2*Cm*Cc,by positivity,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent Mnom u ell δ₁ δ₂ θclip
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  let d:=commonData (withHeight src τ v) C R B
  let rad:=canonicalRadial τ (internalQ Q η₀) dyad
  let V₁:=sourcePlain a b haPlain (p.profile 0) (p.support 0)
  let V₂:=sourcePlain a b haPlain (p.profile 1) (p.support 1)
  let E:=Cc*(C₀+C₁)*diagonalControl rad.profile*(p.control T)^2*
    (1+(|v|+height))^(dc+degree+4*n)*
    Z^(Mnom+εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh)
  have hz:1<Z:=hZ₀.trans_le hZ
  have he:0≤E:=by
    have hd:0≤diagonalControl rad.profile:=by unfold diagonalControl;positivity
    have hz0:0<Z:=zero_lt_one.trans hz
    dsimp [E]
    positivity
  have hleft:∀X₁ X₂:ℝ,∀h₁:0<X₁,∀h₂:0<X₂,X₁≤Z^L → X₂≤Z^L →
      X₁*X₂=d.X₁*d.X₂ → ∀F₁ F₂:Finset (Ideal O),(∀I∈F₁,I≠0) → (∀I∈F₂,I≠0) →
      ∀J,allocatedEnergy τ rad D alloc V₁ V₂ d.slots d.coefficient d.P
        v X₁ X₂ h₁ h₂ F₁ F₂ J≤E:=by
    intro X₁ X₂ h₁ h₂ hc₁ hc₂ hprod F₁ F₂ hF₁ hF₂ J
    apply hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
      src hmatch C R B D alloc J τ dyad hn hwidth p X₁ X₂ h₁ h₂ hc₁ hc₂ F₁ F₂ hF₁ hF₂
      A Mparent Mnom u ell δ₁ δ₂ θclip hu hell hδ₁ hδ₂ hθclip hparent _ hdefect hclip
    simpa only [hprod] using hshift
  have hh:=hcommon src hhi hMs τ v C R hR B D alloc V₁ V₂ hp₁ hp₂ rad
    (fun z hz=>hz.1) E E he he (by
      intro left F₁ hF₁ F₂ hF₂ J hJ
      have hf₁:∀I∈F₁,I≠0:=fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I
        ((Finset.mem_powerset.mp hF₁) hi)).ne_zero
      have hf₂:∀I∈F₂,I≠0:=fun I hi=>(CenteredMomentNaturalRowSource.support_prime (R*C) I
        ((Finset.mem_powerset.mp hF₂) hi)).ne_zero
      cases left
      · exact hleft d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos hY₁ hY₂ d.same_product F₁ F₂ hf₁ hf₂ J
      · exact hleft d.X₁ d.X₂ d.X₁_pos d.X₂_pos hX₁ hX₂ rfl F₁ F₂ hf₁ hf₂ J)
  apply hh.trans_eq
  dsimp [E]
  ring

end SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalReferencePaid. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalReferencePaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_reference_paid_source (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∀θ:α→RayQuotient.Characters M H,
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0<reference →
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=actual_common_paid_source (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε  hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀ θ
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀ θ
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hz:1<Z:=hZ₀.trans_le hZ
  have hz0:0<Z:=zero_lt_one.trans hz
  have hr:1≤ratioPenalty dyad:=le_max_left _ _
  have hr0:0<ratioPenalty dyad:=zero_lt_one.trans_le hr
  have hlog:0≤Real.logb Z (ratioPenalty dyad):=Real.logb_nonneg hz hr
  have hh:=hbound Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent (Real.logb Z reference) u ell
    (δ₁+Real.logb Z (ratioPenalty dyad)) δ₂ θclip hu hell (by linarith) hδ₂ hθclip
    hparent (by linarith) hdefect hclip
  have hpow:Z^(Real.logb Z reference+εchild+εremove+
      (δ₂+u+ell+(δ₁+Real.logb Z (ratioPenalty dyad))/6+θclip/3)+κ*mesh)=
      reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh):=by
    rw [show Real.logb Z reference+εchild+εremove+
      (δ₂+u+ell+(δ₁+Real.logb Z (ratioPenalty dyad))/6+θclip/3)+κ*mesh=
      Real.logb Z reference+Real.logb Z (ratioPenalty dyad)*((1:ℝ)/6)+
        (εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) by ring]
    rw [Real.rpow_add hz0,Real.rpow_add hz0,Real.rpow_logb hz0 hz.ne' href,
      Real.rpow_mul hz0.le,Real.rpow_logb hz0 hz.ne' hr0]
  rw [hpow] at hh
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentEnergyCanonicalReferencePaid

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalUniformReference. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalUniformReference

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem original_subsets_reference_paid (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀Jorig:Finset α,∀θ:Jorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Jorig→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Jorig,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0<reference →
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  have hex (J:Finset α):=actual_reference_paid_source (α:=J) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε  hκ
  choose n T dc Cc hCc hbound using hex
  let n₀:=∑J:Finset α,n J
  let dc₀:=∑J:Finset α,dc J
  let T₀:Finset (ℕ×ℕ):=Finset.univ.biUnion T
  let Ctot:ℝ:=1+∑J:Finset α,Cc J
  have hCt:0<Ctot:=by
    have hh:=Finset.sum_nonneg (fun J (_:J∈(Finset.univ:Finset (Finset α)))=>(hCc J).le)
    dsimp [Ctot];linarith
  refine ⟨n₀,T₀,dc₀,Ctot,hCt,?_⟩
  intro η₀
  let Choices:=ΣJ:Finset α,J→RayQuotient.Characters M H
  let:Fintype (RayQuotient.Characters M H):=Fintype.ofFinite _
  let:Fintype Choices:=inferInstance
  have hchoices (c:Choices):∃Z₀:ℝ,1<Z₀ ∧ _:=hbound c.1 η₀ c.2
  choose Zchoice hZchoice hb using hchoices
  let Z₀:ℝ:=1+∑c:Choices,Zchoice c
  have hZ₀:1<Z₀:=by
    have hn:Nonempty Choices:=⟨⟨∅,fun i=>False.elim (Finset.notMem_empty _ i.property)⟩⟩
    let:Nonempty Choices:=hn
    have hh:=Finset.sum_pos (s:=Finset.univ) (fun c _=>(zero_lt_one.trans (hZchoice c)))
      Finset.univ_nonempty
    dsimp [Z₀];linarith
  refine ⟨Z₀,hZ₀,?_⟩
  intro Jorig θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hZi:Zchoice ⟨Jorig,θ⟩≤Z:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ)
      (fun c _=>(zero_lt_one.trans (hZchoice c)).le) (Finset.mem_univ (⟨Jorig,θ⟩:Choices))
    dsimp [Z₀] at hZ
    linarith
  have hp:=positiveAt_subtype M H hH Jorig W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hh:=hb ⟨Jorig,θ⟩ Z hZi εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hp
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hc:Cc Jorig≤Ctot:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (fun J _=>(hCc J).le) (Finset.mem_univ Jorig)
    dsimp [Ctot];linarith
  have ht:T Jorig⊆T₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨Jorig,Finset.mem_univ _,hx⟩
  have hctrl:p.control (T Jorig)≤p.control T₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hn₀:n Jorig≤n₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ Jorig)
  have hdc₀:dc Jorig≤dc₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ Jorig)
  have hdeg:dc Jorig+degree+4*n Jorig≤dc₀+degree+4*n₀:=by omega
  have hpow:(1+(|v|+height))^(dc Jorig+degree+4*n Jorig)≤
      (1+(|v|+height))^(dc₀+degree+4*n₀):=
    pow_le_pow_right₀ (by linarith [abs_nonneg v]) hdeg
  have hcontrol:=p.control_nonneg (T Jorig)
  have hd:0≤diagonalControl (canonicalRadial τ (internalQ Q η₀) dyad).profile:=by
    unfold diagonalControl;positivity
  have hz0:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hr:0<ratioPenalty dyad:=zero_lt_one.trans_le (le_max_left _ _)
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyCanonicalUniformReference

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalMainPaid. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalMainPaid hiding actual_main_child_from_bands

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

theorem actual_main_child_from_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock τ t Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kmain dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family τ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    let δpaid:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      Cc*(Ideal.absNorm (Rpick*Cpick).radical:ℝ)^εmask*(C₀+C₁)*
        diagonalControl (canonicalRadial (family χ) (internalQ Q η₀) dyad).profile*
        (p.control T)^2*(1+(|v|+height))^(dc+degree+4*n)*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(sigma/3+δpaid/6+θclip/3)+κ*mesh):=by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=original_subsets_reference_paid (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε  hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀
  refine ⟨Z₀,hZ₀,?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource hK hsigma hcost hasource
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hz:1<Z:=hZ₀.trans_le hZ
  have hcost0:0<cost:=zero_lt_one.trans_le hcost
  let input:=child src C R0 B τ t
  let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
  have hKmain:0<Kmain:=by dsimp [Kmain];unfold mainCommonRadius;positivity
  have hP:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hz.le (hw i)
  have hcap':length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤Mdecl:=by
    simpa only [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hcap
  obtain ⟨hδ,hpar,hshift⟩:=actual_main_admission src τ τ C D R0 hC hD hCD E B t hB
    K Z sigma delta reserve cost asource hK hz hcost0 hasource hmod Scols βsource C₂ D₂
    hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical Cpick Rpick hside B₂ hB₂
    κ Mdecl hκsmall hP hcap' hMdecl
  have hm:=matches_child M H hH hmatch C R0 B τ t
  have caps₁:=common_raw_caps src C R0 B τ t (Z^L) hX₁ hX₂ hY₁ hY₂
  have caps₂:=common_raw_caps input Cpick Rpick B₂ (family χ) v (Z^L)
    caps₁.1 caps₁.2.1 caps₁.2.2.1 caps₁.2.2.2
  have hτnorm:0<(τ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hq:(τ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ):=by nlinarith
  have hdef:=actual_width_le_reference hfamily t Scols βsource Rwindow rows Wkernel Kmain hKmain dyad
    hphysical (cost*(τ.modulus.absNorm:ℝ)) Z hq hz χ
  have hn:=actual_dyad_ge_one t Scols βsource Rwindow rows Wkernel Kmain dyad hphysical
  have hh:=hbound (CenteredMomentCommonProfile.liveIndices B.val) (fun i=>θ i.val)
    Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val) v height mesh hmesh
    (fun i=>hw i.val) (fun i=>hwm i.val) (fun i=>hwL i.val) (fun i=>hσlo i.val)
    (fun i=>hσhi i.val) hheight (fun i=>hfreq i.val) input hm
    (fun i=>hhi i.val) (fun i=>hMs i.val) Cpick Rpick B₂ Dalloc alloc hRpick
    (family χ) dyad hn hwidth p hp₁ hp₂ caps₂.1 caps₂.2.1 caps₂.2.2.1 caps₂.2.2.2
    (Real.logb Z (volume src)) Mdecl (envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad)
    0 (sigma/3) _ 0 θclip (envelope_pos _ (mul_pos hcost0 hτnorm) _ _ hC₂ _ _) le_rfl
    (by positivity) hδ le_rfl hθclip
    (by simpa only [input,CenteredMomentAmplificationChildInput.child,commonData,withHeight,hmatch.scale,
      Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hpar)
    (by simpa only [OAI.SevenEighths.CenteredMomentAllocatedChildCapacity.preVolume,commonData,withHeight,
      zero_add] using hshift)
    (by linarith) hclip
  simpa only [zero_add] using hh

end SevenEighths.CenteredMomentEnergyCanonicalMainPaid

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalMainUniform. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainUniform

open OAI.SevenEighths.CenteredMomentEnergyCanonicalMainUniform hiding actual_main_uniform_child

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

theorem actual_main_uniform_child (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 BR BC θsource:ℝ)
    (hlower:0<lower)(ha0:0<a0)(hθsource:0<θsource):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock τ t Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kmain dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family τ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    (Rpick.absNorm:ℝ)≤Z^BR → (Cpick.absNorm:ℝ)≤Z^BC →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
        ((BR+BC)*εmask+(εchild+εremove+
          (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
            delta+reserve+θsource)/6+θclip/3)+κ*mesh))*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad*
        (ratioPenalty dyad)^((1:ℝ)/6)*(1+‖v‖)^(2*(dc+degree+4*n))  :=by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalMainPaid.actual_main_child_from_bands (α:=α) M H hH
      W aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall  hκ
  obtain ⟨Zr,hZr,hr⟩:=OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidReserve.eventually_actual_amplified_reserves
    N lower upper 1 a0 θsource hlower (by norm_num) ha0 hθsource
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Zi,hZi,hi⟩:=hbound η₀
  refine ⟨max Zi Zr,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlowerBeta hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick hRN hCN B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZrZ:Zr≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  have hh:=hi θ Z hZiZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource
    hK hsigma hcost hasource Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad
    hlowerBeta hphysical family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hsmall:sourceReserve src (child src C R0 B τ t) C D Z delta reserve cost asource≤
      delta+reserve+θsource:=
    (hr Z hZrZ src hcard hlowerSrc hupperSrc C D R0 hC.1 hD.1 B τ t delta reserve cost asource
      hdelta hreserve hcost haSource).1
  have hCp:Cpick≠0:=by rcases hside with rfl|rfl;exact hC₂.1;exact hD₂.1
  have href:0<envelopeRef (cost*(τ.modulus.absNorm:ℝ)) C₂ D₂ U dyad:=
    envelope_pos _ (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
      C₂ D₂ hC₂ U dyad
  apply hh.trans
  apply OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.paid_rhs_fit Cc C₀ C₁ p T Rpick Cpick hRpick hCp
    (family χ) (internalQ Q η₀) dyad v height (dc+degree+4*n) Z BR BC εmask
    _ _ _ _ hCc.le hC₀ hC₁ hheight hz.le hεmask.le hRN hCN
  · linarith
  · exact href.le
  · exact zero_le_one.trans (le_max_left _ _)

end SevenEighths.CenteredMomentEnergyCanonicalMainUniform

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalMainGaussian. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainGaussian

open OAI.SevenEighths.CenteredMomentEnergyCanonicalMainGaussian hiding actual_main_gaussian_from_bands

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_main_gaussian_from_bands
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input (R0*C) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    (∀q∈liveLabels input.η Scols β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀dyad:SourceBlocks q.val.1 q.val.2 U Kmain (frequencyRadius (nominal input Kmain) Z ξ)
        (sourceRadius input),
      physicalBlock input.η input.t (activeSource Scols β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U
        (frequencyRadius (nominal input Kmain) Z ξ)
        (partRows false input.η χ₀ (internalQ Q η₀) m q.val.1 q.val.2 U
          (frequencyRadius (nominal input Kmain) Z ξ))
        CenteredMomentFirstAmplificationChoice.ballProfile Kmain (fun i=>(dyad i:ℤ))≠0 →
      ∀χ:RayCharacter,Real.logb Z (dyadicScale (dyad 1))+
        Real.logb Z ((family q U χ).modulus.absNorm:ℝ)≤Mcap) →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh))
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc t
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kmain t
          (cost*(τ.modulus.absNorm:ℝ)) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,hmain⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalMainUniform.actual_main_uniform_child (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall  hκ
      N lower upper a0 Bcap Bcap θsource hlower ha0 hθsource
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hgauss⟩:=
    actual_subsets_seeded_gaussian_power a b haPlain hbPlain lows highs hhighs
      CenteredMomentFirstAmplificationChoice.ballProfile (dc+degree+4*n) (dc+degree+4*n)
      N upper (max 1 b) (max 1 b) hupper (le_max_left _ _) (le_max_left _ _)
      εsrc δsrc θsrc Bcap Bseed ξ saving hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Zm,hZm,hm⟩:=hmain η₀
  obtain ⟨Kc,hKc,hevent⟩:=hgauss (internalQ Q η₀) hQ0 hQt hQ72
  obtain ⟨Zg,hZg⟩:=Filter.eventually_atTop.1 hevent
  refine ⟨Kc,hKc,max Zm Zg,lt_of_lt_of_le hZm (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hsourceLower Scols β hScols hβ
  let input:=child src C R0 B τ t
  let Km:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
  have hZmZ:Zm≤Z:=(le_max_left _ _).trans hZ
  have hgZ:=hZg Z ((le_max_right _ _).trans hZ)
  have hz:1<Z:=hgZ.1
  have hP:∀i,1≤ input.P i:=by
    intro i
    change 1≤src.P i.val
    rw [hmatch.scale]
    exact Real.one_le_rpow hz.le (hw i.val)
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices B.val)≤N:=
    (child_card B.val).trans hcard
  have hlowerBeta (I:Ideal O)(hne:coefficient input (R0*C) seed I≠0):
      asource*volume input≤(I.absNorm:ℝ):=by
    apply (mul_le_mul_of_nonneg_right hsourceLower (volume_pos input).le).trans
    apply OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.actual_lower_support N lower a hlower haPlain
      input hcardInput hlowerSrc ?_ ?_ (R0*C) seed I hne
    · intro x hx
      change src.W₁ x≠0 at hx
      rw [←hp₁] at hx
      exact (p.support 0 hx).1
    · intro x hx
      change src.W₂ x≠0 at hx
      rw [←hp₂] at hx
      exact (p.support 1 hx).1
  have hsource:=hgZ.2 (CenteredMomentCommonProfile.liveIndices B.val) input p
    (fun i=>hloSrc i.val) (fun i=>hhiSrc i.val) hP hp₁.symm hp₂.symm (mass src)
    hupperSrc hcardInput hb1 hb2 hb1max hb2max (child_mass src C R0 B τ t)
    (R0*C) seed hready.puncture_ne hseed hseed0 hseedcap hready.source_nonneg hready.source_cap
    hready.conductor_cap hready.puncture_cap
  change Scols=finiteColumns (Fintype.piFinset input.pools) at hScols
  change β=coefficient input (R0*C) seed at hβ
  dsimp only at hsource
  subst Scols β
  obtain ⟨family,hfamily,hbound⟩:=hsource
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm0 hml hm2 hwidth r hr1 hr2 hr3 hr4
  let Ec:=OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh))
  have hEc:0≤Ec:=OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient_nonneg
    Cc C₀ C₁ p T height (dc+degree+4*n) Z _ hCc.le hC₀ hC₁ hheight (zero_le_one.trans hz.le)
  have hpzero (j:Fin 2):p.profile j 0=0:=by
    by_contra hn
    exact (not_le_of_gt haPlain) ((p.support j hn).1)
  have hz1:input.W₁ 0=0:=by change src.W₁ 0=0;rw [←hp₁];exact hpzero 0
  have hz2:input.W₂ 0=0:=by change src.W₂ 0=0;rw [←hp₂];exact hpzero 1
  apply hbound χ₀ m hm0 hml hm2 Km (nominal input Km) hready.scale_pos hready.volume_cap
    hready.nominal_cap (le_refl _) hready.frequency_pos hready.frequency_cap
    (cost*(τ.modulus.absNorm:ℝ))
    (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
    Ec Ec hEc hEc ?_ ?_ r hr1 hr2 hr3 hr4
  all_goals
    intro q hq U dyad hphysical D0 hD0 hD0cap hD0sq χ v B₂ hB₂ alloc halloc
    have hg:=actual_common_gates input (R0*C) seed hseed hz1 hz2 q.val.1 q.val.2 q.property
    have hs:=commonLabels_supported (activeSource _ _) _ _ q.property
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.1 (R0*C) (Or.inl rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.1.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.2 (R0*C) (Or.inr rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.2.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip

end SevenEighths.CenteredMomentEnergyCanonicalMainGaussian

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparated. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSeparated

open OAI.SevenEighths.CenteredMomentEnergyCanonicalMainSeparated hiding actual_main_separated_gaussian

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_main_separated_gaussian
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve cost asource:ℝ,0<K → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input (R0*C) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh))
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc t
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kmain t
          (cost*(τ.modulus.absNorm:ℝ)) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalMainGaussian.actual_main_gaussian_from_bands (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  let Zw:=OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth.threshold N upper sigma hupper hsigma
  refine ⟨Kc,hKc,max Zi Zw,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZw:Zw≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZiZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma.le hcost hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  apply hbound χ₀ m hm hml hm2 ?_ r hr1 hr2 hr3 hr4
  intro q hq U dyad hphysical χ
  have hs:=commonLabels_supported (activeSource Scols β) _ _ q.property
  have hη:(src.η.modulus.absNorm:ℝ)≤Z^(Real.logb Z (src.η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz)
      (norm_pos src.η.modulus src.η.modulus_ne_bot)]
  have hh:=OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth.main_child_width N upper sigma hupper hsigma
    Z hZw src hcard hupperSrc C D R0 hC hD hCD E B τ t hB hmod K delta reserve ξ
    (Real.logb Z (src.η.modulus.absNorm:ℝ)) Mwidth hK hdelta hreserve hξsmall hη hMwidth
    (activeSource Scols β) β q.val.1 q.val.2 hs.1 hs.2 U (family q U) (hfamily q U)
    _ CenteredMomentFirstAmplificationChoice.ballProfile (fun i=>(dyad i:ℤ)) hphysical χ
  exact hh.le.trans hdrop

end SevenEighths.CenteredMomentEnergyCanonicalMainSeparated

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalMainSeparatedPower. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower

open OAI.SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower hiding actual_main_separated_power

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

theorem actual_main_separated_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve cost asource:ℝ,0<K → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input (R0*C) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n);
    let Hweights:=coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J
      (internalQ Q η₀) Kc t εsrc (seed.absNorm:ℝ)
      (fixedFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap cost Ebase t
        (OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
        (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile);
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,Hweights j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalMainSeparated.actual_main_separated_gaussian (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Kc,hKc,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  have hg:=hbound χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n)
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hE:0≤Ebase:=by dsimp [Ebase];have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile;positivity
  have hloProd:=OAI.SevenEighths.CenteredMomentEnergyOriginalProfileControl.lower_product
    (child src C R0 B τ t) N lower hlower ((live_card_le B.val).trans hcard)
    (fun i=>hlowerSrc.trans (src.lower_le i.val))
  have hlo:OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a≤
      (∏i,(child src C R0 B τ t).lo i)*a*a:=by
    unfold OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hloProd (sq_nonneg a)
  have hcoef:=OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients.main_coefficients
    N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc
    Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving
    (mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve)
    t (τ.modulus.absNorm:ℝ) cost Ebase (sigma/3)
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid r
    (∏i,(child src C R0 B τ t).lo i) a
    (OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
    (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile
    (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
    (le_trans zero_le_one (le_max_left _ _)) hKc.le (Nat.cast_nonneg _) hCm.le hCe hz hE
    (by unfold mainCommonRadius;positivity)
    (OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain) hlo
  have hexp:
      (Bcap+Bcap)*εmask+(εchild+εremove+
        (sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3)+κ*mesh)=
      sigma/3+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))/6+paid :=by
    dsimp [paid];ring
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  have hh:=mul_le_mul_of_nonneg_right (hcoef j)
    (Real.rpow_nonneg (volume_pos (child src C R0 B τ t)).le (powers εsrc j))
  simpa only [OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient,hexp,Ebase,paid] using hh

end SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalMainHomogeneous. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous hiding actual_main_homogeneous

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

theorem actual_main_homogeneous
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalMainSeparatedPower.actual_main_separated_power (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  have hlo:=OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain
  obtain ⟨Uprofile,Jheight,hweights⟩:=
    OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.actual_weights (a:=a) (b:=b)
      N upper (max 1 b) (max 1 b) ((max 1 Mslot)^N)
      (OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a)
      Cm Ce Cd Ct Cc cost εsrc δsrc θsrc Bcap J (dc+degree+4*n) (dc+degree+4*n)
      Sp T Sf CenteredMomentFirstAmplificationChoice.ballProfile
      (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
      (le_trans zero_le_one (le_max_left _ _)) (by positivity) hlo
      hCm.le hCe hCd.le hCt.le hCc.le (zero_le_one.trans hcost)
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hwbound⟩:=hweights (internalQ Q η₀) Kc hKc.le
  refine ⟨Cbound,hCbound,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  let input:=child src C R0 B τ t
  let Scols:=finiteColumns (Fintype.piFinset input.pools)
  let β:=coefficient input (R0*C) seed
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β rfl rfl
  have hg:=hbound 1 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hmass:mass src≤(max 1 Mslot)^N:=
    OAI.SevenEighths.CenteredMomentEnergyOriginalProfileControl.slot_product_le src N (max 1 Mslot)
      (le_max_left _ _) hcard (fun i=>(hMs i).trans (le_max_right _ _))
  have hnseed:1≤(seed.absNorm:ℝ):=norm_ge_one seed hseed0
  have hh:=hwbound p Z t height (mass src) (seed.absNorm:ℝ) C₀ C₁
    hz hheight (mass_nonneg src) hmass hnseed hC₀ hC₁
  dsimp only at hh
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos input).le _)
  apply mul_le_mul_of_nonneg_right (hh j)
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold mainCommonRadius
  all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalMainSubsets. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalMainSubsets

open OAI.SevenEighths.CenteredMomentEnergyCanonicalMainSubsets hiding actual_original_subsets_main_power

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

theorem actual_original_subsets_main_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  have hmain (Aorig:Finset α):=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalMainHomogeneous.actual_main_homogeneous (α:=Aorig) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource (fun i=>lows i.val) (fun i=>highs i.val)
      (fun i=>hhighs i.val) εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  choose Uj Jj hj using hmain
  let Uprofile:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Jheight:ℕ:=∑Aorig:Finset α,Jj Aorig
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  choose Cj hCj Zj hZj hconsume using fun Aorig=>hj Aorig η₀ Q hQM hQ0 hQt hQ72
  let Cbound:ℝ:=1+∑Aorig:Finset α,Cj Aorig
  let Z₀:ℝ:=2+∑Aorig:Finset α,|Zj Aorig|
  have hCbound:0<Cbound:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>(hCj Aorig).le)
    dsimp [Cbound];linarith
  have hZ₀:1<Z₀:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>abs_nonneg (Zj Aorig))
    dsimp [Z₀];linarith
  have hCC (Aorig:Finset α):Cj Aorig≤Cbound:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>(hCj A).le)
      (Finset.mem_univ Aorig)
    dsimp [Cbound];linarith
  have hZZ (Aorig:Finset α):Zj Aorig≤Z₀:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>abs_nonneg (Zj A))
      (Finset.mem_univ Aorig)
    dsimp [Z₀];linarith [le_abs_self (Zj Aorig)]
  refine ⟨Cbound,hCbound,Z₀,hZ₀,?_⟩
  intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  have hposA:=positiveAt_subtype M H hH Aorig Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hg:=hconsume Aorig θ Z ((hZZ Aorig).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hposA
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hsub:Uj Aorig⊆Uprofile:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨Aorig,Finset.mem_univ _,hx⟩
  have hp:p.control (Uj Aorig)≤p.control Uprofile:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hJ:Jj Aorig≤Jheight:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ Aorig)
  have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hp0:=p.control_nonneg (Uj Aorig)
  have hp1:=p.control_nonneg Uprofile
  have hh:(1+|t|+height)^(Jj Aorig)≤(1+|t|+height)^Jheight:=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hfront:Cj Aorig*(C₀+C₁+1)*(p.control (Uj Aorig))^2*(1+|t|+height)^(Jj Aorig)≤
      Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight:=by
    have hc:=hCC Aorig
    have hc0:0≤Cj Aorig:=(hCj Aorig).le
    gcongr
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
  apply mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold mainCommonRadius
  all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalMainSubsets

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalNestedReference. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalNestedReference

open OAI.SevenEighths.CenteredMomentEnergyCanonicalNestedReference hiding nested_original_subsets_reference_paid

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem nested_original_subsets_reference_paid (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκ:1 ≤ κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀Jparent:Finset α,∀Jorig:Finset Jparent,∀θ:Jorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀(Q:Ideal O),Q≤M →
    ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Jorig→ℝ)(v height mesh:ℝ),
    0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
    (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Jorig,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C R:Ideal O)(B:actualAllocations src.pools C)(D:Ideal O)
      (alloc:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),R≠0 →
    ∀(τ:Character)(dyad:Fin 4→ℤ),∀_hn:1≤CenteredMomentSectorLocalization.dyadicScale (dyad 1),
    Real.logb Z (CenteredMomentSectorLocalization.dyadicScale (dyad 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Mcap →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    let d:=commonData (withHeight src τ v) C R B
    d.X₁≤Z^L → d.X₂≤Z^L → d.Y₁≤Z^L → d.Y₂≤Z^L →
    ∀A Mparent reference u ell δ₁ δ₂ θclip:ℝ,0<reference →
    0≤u → 0≤ell → 0≤δ₁ → 0≤δ₂ → 0≤θclip →
    A+(6*κ-1)*(∑i:CenteredMomentCommonProfile.liveIndices B.val,w i.val)≤Mparent →
    Real.logb Z (d.X₁*d.X₂*∏i:CenteredMomentCommonProfile.liveIndices B.val,src.P i.val)-Real.logb Z reference≤
      A-Mparent+6*(u+ell)+δ₁+Real.logb Z (ratioPenalty dyad) →
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z (τ.modulus.absNorm:ℝ)-Real.logb Z reference≤δ₂ →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy d (canonicalRadial τ (internalQ Q η₀) dyad) D alloc ≤
      Cc*(Ideal.absNorm (R*C).radical:ℝ)^εmask*(C₀+C₁)*diagonalControl (CenteredMomentSecondNonexceptionalChosenBlock.canonicalRadial τ (internalQ Q η₀) dyad).profile*
        (p.control T)^2*
        (1+(|v|+height))^(dc+degree+4*n)*
        reference*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(δ₂+u+ell+δ₁/6+θclip/3)+κ*mesh) := by
  let Pairs:=ΣJparent:Finset α,Finset Jparent
  have hex (J:Pairs):=actual_reference_paid_source (α:=J.2) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε  hκ
  choose n T dc Cc hCc hbound using hex
  let n₀:=∑J:Pairs,n J
  let dc₀:=∑J:Pairs,dc J
  let T₀:Finset (ℕ×ℕ):=Finset.univ.biUnion T
  let Ctot:ℝ:=1+∑J:Pairs,Cc J
  have hCt:0<Ctot:=by
    have hh:=Finset.sum_nonneg (fun J (_:J∈(Finset.univ:Finset Pairs))=>(hCc J).le)
    dsimp [Ctot];linarith
  refine ⟨n₀,T₀,dc₀,Ctot,hCt,?_⟩
  intro η₀
  let Choices:=ΣJ:Pairs,J.2→RayQuotient.Characters M H
  let:Fintype (RayQuotient.Characters M H):=Fintype.ofFinite _
  let:Fintype Choices:=inferInstance
  have hchoices (c:Choices):∃Z₀:ℝ,1<Z₀ ∧ _:=hbound c.1 η₀ c.2
  choose Zchoice hZchoice hb using hchoices
  let Z₀:ℝ:=1+∑c:Choices,Zchoice c
  have hZ₀:1<Z₀:=by
    have hn:Nonempty Choices:=⟨⟨⟨∅,∅⟩,fun i=>False.elim (Finset.notMem_empty _ i.property)⟩⟩
    let:Nonempty Choices:=hn
    have hh:=Finset.sum_pos (s:=Finset.univ) (fun c _=>(zero_lt_one.trans (hZchoice c)))
      Finset.univ_nonempty
    dsimp [Z₀];linarith
  refine ⟨Z₀,hZ₀,?_⟩
  intro Jparent Jorig θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
  dsimp only
  intro hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hZi:Zchoice ⟨⟨Jparent,Jorig⟩,θ⟩≤Z:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ)
      (fun c _=>(zero_lt_one.trans (hZchoice c)).le) (Finset.mem_univ (⟨⟨Jparent,Jorig⟩,θ⟩:Choices))
    dsimp [Z₀] at hZ
    linarith
  have hp₀:=positiveAt_subtype M H hH Jparent W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hp:=positiveAt_subtype M H hH Jorig W bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hp₀
  have hh:=hb ⟨⟨Jparent,Jorig⟩,θ⟩ Z hZi εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hp
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq
    src hmatch hhi hMs C R B D alloc hR τ dyad hn hwidth p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ A Mparent reference u ell δ₁ δ₂ θclip href
    hu hell hδ₁ hδ₂ hθclip hparent hshift hdefect hclip
  have hc:Cc ⟨Jparent,Jorig⟩≤Ctot:=by
    have hh:=Finset.single_le_sum (s:=Finset.univ) (fun J _=>(hCc J).le) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
    dsimp [Ctot];linarith
  have ht:T ⟨Jparent,Jorig⟩⊆T₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨⟨Jparent,Jorig⟩,Finset.mem_univ _,hx⟩
  have hctrl:p.control (T ⟨Jparent,Jorig⟩)≤p.control T₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono ht) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hn₀:n ⟨Jparent,Jorig⟩≤n₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
  have hdc₀:dc ⟨Jparent,Jorig⟩≤dc₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨Jparent,Jorig⟩:Pairs))
  have hdeg:dc ⟨Jparent,Jorig⟩+degree+4*n ⟨Jparent,Jorig⟩≤dc₀+degree+4*n₀:=by omega
  have hpow:(1+(|v|+height))^(dc ⟨Jparent,Jorig⟩+degree+4*n ⟨Jparent,Jorig⟩)≤
      (1+(|v|+height))^(dc₀+degree+4*n₀):=
    pow_le_pow_right₀ (by linarith [abs_nonneg v]) hdeg
  have hcontrol:=p.control_nonneg (T ⟨Jparent,Jorig⟩)
  have hd:0≤diagonalControl (canonicalRadial τ (internalQ Q η₀) dyad).profile:=by
    unfold diagonalControl;positivity
  have hz0:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hr:0<ratioPenalty dyad:=zero_lt_one.trans_le (le_max_left _ _)
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyCanonicalNestedReference

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalErrorPaid. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalErrorPaid hiding actual_error_child_from_bands

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][instα:DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalMainPaid ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalNestedReference

open OAI.SevenEighths.CenteredMomentEnergyCanonicalMainPaid hiding actual_main_child_from_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalNestedReference hiding nested_original_subsets_reference_paid

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open OAI.SevenEighths.CenteredMomentEnergyActiveChildRestoration

open OAI.SevenEighths.CenteredMomentEnergyActiveChildRestoration

theorem actual_error_child_from_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock υ v0 Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kerror dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family υ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    let δpaid:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      Cc*(Ideal.absNorm (Rpick*Cpick).radical:ℝ)^εmask*(C₀+C₁)*
        diagonalControl (canonicalRadial (family χ) (internalQ Q η₀) dyad).profile*
        (p.control T)^2*(1+(|v|+height))^(dc+degree+4*n)*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+(errorRemoval prime Z k+δpaid/6+θclip/3)+κ*mesh):=by
  cases Subsingleton.elim instα (Classical.decEq α)
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=nested_original_subsets_reference_paid (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε  hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀
  refine ⟨Z₀,hZ₀,?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource hK hsigma hcost hasource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  subst input
  have hz:1<Z:=hZ₀.trans_le hZ
  have hcost0:0<cost:=zero_lt_one.trans_le hcost
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let restored:=restoredError src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  have heInput:input=activeInput restored:=by
    exact error_source_active src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let B₂a:=castAllocation input (activeInput restored) heInput Cpick B₂
  let B₂r:=restoreAllocation restored Cpick B₂a
  let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
  have hKerror:0<Kerror:=by dsimp [Kerror];unfold errorCommonRadius;positivity
  have hP:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hz.le (hw i)
  have hcap':length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤Mdecl:=by
    simpa only [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hcap
  obtain ⟨hδ,hpar,hshift⟩:=actual_active_error_admission src τ υ C D R0 hC hD hCD E B t hB
    K Z sigma delta reserve cost asource hK hz hcost0 hasource prime hprime k hk hsigma hprimeScale
    hslot Bp v0 hmod Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    Cpick Rpick hside B₂ hB₂ κ Mdecl hκsmall hP hcap' hMdecl
  have hm:=restoredError_matches M H hH hmatch C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  have caps₁:=common_raw_caps src C R0 B τ t (Z^L) hX₁ hX₂ hY₁ hY₂
  have caps₂:=common_raw_caps (child src C R0 B τ t) ((Ideal.span {prime})^k) (R0*C)
    (restoreAllocation (child src C R0 B τ t) ((Ideal.span {prime})^k) Bp) υ v0 (Z^L)
    caps₁.1 caps₁.2.1 caps₁.2.2.1 caps₁.2.2.2
  have caps₃:=common_raw_caps restored Cpick Rpick B₂r (family χ) v (Z^L)
    caps₂.1 caps₂.2.1 caps₂.2.2.1 caps₂.2.2.2
  have hτnorm:0<(τ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hqpos:0<cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k):=by positivity
  have hdef:=actual_width_le_reference hfamily v0 Scols βsource Rwindow rows Wkernel Kerror hKerror dyad
    hphysical (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) Z hυ hz χ
  have hn:=actual_dyad_ge_one v0 Scols βsource Rwindow rows Wkernel Kerror dyad hphysical
  have hrem:0≤errorRemoval prime Z k:=by
    have hn:0≤Real.logb Z (normValue prime):=by linarith
    unfold errorRemoval
    positivity
  have hsum:(∑i:CenteredMomentCommonProfile.liveIndices B₂.val,Real.logb Z (input.P i.val))=
      ∑i:CenteredMomentCommonProfile.liveIndices B₂.val,w i.val.val.val:=by
    apply Finset.sum_congr rfl
    intro i hi
    change Real.logb Z (src.P i.val.val.val)=w i.val.val.val
    rw [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne']
  have hparw:Real.logb Z (volume src)+(6*κ-1)*
      (∑i:CenteredMomentCommonProfile.liveIndices B₂r.val,w i.val.val.val)≤Mdecl:=by
    rw [hsum] at hpar
    have heSum := (restored_slot_sum restored Cpick B₂a (fun i=>w i.val.val)).trans
      (cast_slot_sum input (activeInput restored) heInput Cpick B₂ (fun i=>w i.val.val))
    exact (congrArg (fun x=>Real.logb Z (volume src)+(6*κ-1)*x) heSum).trans_le hpar
  have hshiftw:
      Real.logb Z ((commonData (withHeight restored (family χ) v) Cpick Rpick B₂r).X₁*
        (commonData (withHeight restored (family χ) v) Cpick Rpick B₂r).X₂*
        ∏i:CenteredMomentCommonProfile.liveIndices B₂r.val,restored.P i.val)-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)≤
      Real.logb Z (volume src)-Mdecl+6*(errorRemoval prime Z k+0)+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          sourceReserve src input C D Z delta reserve cost asource)+Real.logb Z (ratioPenalty dyad):=by
    change Real.logb Z (OAI.SevenEighths.CenteredMomentAllocatedChildCapacity.preVolume
      (commonData (withHeight restored (family χ) v) Cpick Rpick B₂r))-_≤_
    have hpv:= (restored_preVolume restored Cpick Rpick B₂a (family χ) v).trans
      ((cast_preVolume input (activeInput restored) heInput Cpick Rpick B₂ (family χ) v).trans
        (common_preVolume_height input Cpick Rpick B₂ (family χ) υ v v0))
    calc
      _ = Real.logb Z (OAI.SevenEighths.CenteredMomentAllocatedChildCapacity.preVolume
          (commonData (withHeight input υ v0) Cpick Rpick B₂)) -
          Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad) :=
        congrArg (fun x=>Real.logb Z x - Real.logb Z
          (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)) hpv
      _ ≤ _ := by
        dsimp only [input]
        simpa only [add_zero] using hshift
  have hh:=hbound (CenteredMomentCommonProfile.liveIndices B.val)
    (CenteredMomentCommonProfile.liveIndices Bp.val) (fun i=>θ i.val.val)
    Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    (fun i=>w i.val.val) (fun i=>σ i.val.val) (fun i=>freq i.val.val) v height mesh hmesh
    (fun i=>hw i.val.val) (fun i=>hwm i.val.val) (fun i=>hwL i.val.val) (fun i=>hσlo i.val.val)
    (fun i=>hσhi i.val.val) hheight (fun i=>hfreq i.val.val)
  have hh := hh restored hm (fun i=>hhi i.val.val) (fun i=>hMs i.val.val)
  have hh := hh Cpick Rpick B₂r
  let allocA:=castDivisorAllocation input (activeInput restored) heInput Cpick B₂ Dalloc alloc
  let allocR:=restoreDivisorAllocation restored Cpick B₂a Dalloc allocA
  have hh := hh Dalloc allocR hRpick
  have hh := hh (family χ) dyad hn hwidth
  have hh := hh p hp₁ hp₂
  have hh := hh caps₃.1 caps₃.2.1 caps₃.2.2.1 caps₃.2.2.2
  have hh := hh (Real.logb Z (volume src)) Mdecl
    (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)
    (errorRemoval prime Z k) 0
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource)
    0 θclip (envelope_pos _ hqpos _ _ hC₂ _ _)
    hrem le_rfl hδ le_rfl hθclip
  have hh := hh hparw
  have hh := hh hshiftw
  have hh := hh (by linarith only [hdef]) hclip
  have he := (cast_child_energy input (activeInput restored) heInput Cpick Rpick B₂ (family χ) v Dalloc alloc
    (canonicalRadial (family χ) (internalQ Q η₀) dyad)).trans
      (restored_child_energy restored Cpick Rpick B₂a (family χ) v Dalloc allocA
        (canonicalRadial (family χ) (internalQ Q η₀) dyad))
  apply he.trans_le
  simpa only [zero_add,add_zero] using hh

end SevenEighths.CenteredMomentEnergyCanonicalErrorPaid

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalErrorUniform. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorUniform

open OAI.SevenEighths.CenteredMomentEnergyCanonicalErrorUniform hiding actual_error_uniform_child

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalMainPaid ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalNestedReference

open OAI.SevenEighths.CenteredMomentEnergyCanonicalMainPaid hiding actual_main_child_from_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalNestedReference hiding nested_original_subsets_reference_paid

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open OAI.SevenEighths.CenteredMomentEnergyActiveChildRestoration

open OAI.SevenEighths.CenteredMomentEnergyActiveChildRestoration

theorem actual_error_uniform_child (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(L:ℝ)(hL:0≤L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 BR BC θsource:ℝ)
    (hlower:0<lower)(ha0:0<a0)(hθsource:0<θsource):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤M → ∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock υ v0 Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kerror dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family υ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    (Rpick.absNorm:ℝ)≤Z^BR → (Cpick.absNorm:ℝ)≤Z^BC →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
        ((BR+BC)*εmask+(εchild+εremove+errorRemoval prime Z k+
          (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
            delta+reserve+θsource)/6+θclip/3+κ*mesh))*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad*
        (ratioPenalty dyad)^((1:ℝ)/6)*(1+‖v‖)^(2*(dc+degree+4*n))  :=by
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalErrorPaid.actual_error_child_from_bands (α:=α) M H hH
      W aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall  hκ
  obtain ⟨Zr,hZr,hr⟩:=OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidReserve.eventually_source_reserve
    N lower upper 1 a0 θsource hlower (by norm_num) ha0 hθsource
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Zi,hZi,hi⟩:=hbound η₀
  refine ⟨max Zi Zr,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlowerBeta hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick hRN hCN B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZrZ:Zr≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  have hh:=hi θ Z hZiZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource
    hK hsigma hcost hasource prime hprime k hk hprimeScale hslot Bp υ v0 hυ
    input hinput
    Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad
    hlowerBeta hphysical family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  have hupperInput:input.upper≤upper:=by rw [hinput];exact hupperSrc
  have hchild:Fintype.card (CenteredMomentCommonProfile.liveIndices B.val)≤N:=
    (CenteredMomentAmplificationChildSourceCaps.live_card_le B.val).trans hcard
  have herr:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤N:=
    (CenteredMomentAmplificationChildSourceCaps.live_card_le Bp.val).trans hchild
  have hsmall:sourceReserve src input C D Z delta reserve cost asource≤delta+reserve+θsource:=
    hr Z hZrZ src input hcard herr hlowerSrc hupperInput C D hC.1 hD.1
      delta reserve cost asource hdelta hreserve hcost haSource
  have hCp:Cpick≠0:=by rcases hside with rfl|rfl;exact hC₂.1;exact hD₂.1
  have hqpos:0<cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k):=
    mul_pos (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _)
  have href:0<envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad:=
    envelope_pos _ hqpos C₂ D₂ hC₂ U dyad
  apply hh.trans
  apply OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.paid_rhs_fit Cc C₀ C₁ p T Rpick Cpick hRpick hCp
    (family χ) (internalQ Q η₀) dyad v height (dc+degree+4*n) Z BR BC εmask
    _ _ _ _ hCc.le hC₀ hC₁ hheight hz.le hεmask.le hRN hCN
  · linarith
  · exact href.le
  · exact zero_le_one.trans (le_max_left _ _)

end SevenEighths.CenteredMomentEnergyCanonicalErrorUniform

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalErrorGaussian. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorGaussian

open OAI.SevenEighths.CenteredMomentEnergyCanonicalErrorGaussian hiding actual_error_gaussian_from_bands

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_error_gaussian_from_bands
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0<K → 0≤sigma → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    Ready input ((R0*C)*(Ideal.span {prime})^k) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input ((R0*C)*(Ideal.span {prime})^k) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    (∀q∈liveLabels input.η Scols β,∀U:Finset (CommonIndex q.val.1 q.val.2),
      ∀dyad:SourceBlocks q.val.1 q.val.2 U Kerror (frequencyRadius (nominal input Kerror) Z ξ)
        (sourceRadius input),
      physicalBlock input.η input.t (activeSource Scols β) β q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U
        (frequencyRadius (nominal input Kerror) Z ξ)
        (partRows false input.η χ₀ (internalQ Q η₀) m q.val.1 q.val.2 U
          (frequencyRadius (nominal input Kerror) Z ξ))
        CenteredMomentFirstAmplificationChoice.ballProfile Kerror (fun i=>(dyad i:ℤ))≠0 →
      ∀χ:RayCharacter,Real.logb Z (dyadicScale (dyad 1))+
        Real.logb Z ((family q U χ).modulus.absNorm:ℝ)≤Mcap) →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+errorRemoval prime Z k+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh))
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^k) seed CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc v0
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kerror v0
          (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,hmain⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalErrorUniform.actual_error_uniform_child (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL
      degree S ha hWs hW hMcap hLs hε hκsmall  hκ
      N lower upper a0 Bcap Bcap θsource hlower ha0 hθsource
  obtain ⟨J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hgauss⟩:=
    actual_nested_subsets_seeded_gaussian_power a b haPlain hbPlain lows highs hhighs
      CenteredMomentFirstAmplificationChoice.ballProfile (dc+degree+4*n) (dc+degree+4*n)
      N upper (max 1 b) (max 1 b) hupper (le_max_left _ _) (le_max_left _ _)
      εsrc δsrc θsrc Bcap Bseed ξ saving hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Zm,hZm,hm⟩:=hmain η₀
  obtain ⟨Kc,hKc,hevent⟩:=hgauss (internalQ Q η₀) hQ0 hQt hQ72
  obtain ⟨Zg,hZg⟩:=Filter.eventually_atTop.1 hevent
  refine ⟨Kc,hKc,max Zm Zg,lt_of_lt_of_le hZm (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  subst input
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hasourceFactor Scols β hScols hβ
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let Km:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
  have hZmZ:Zm≤Z:=(le_max_left _ _).trans hZ
  have hgZ:=hZg Z ((le_max_right _ _).trans hZ)
  have hz:1<Z:=hgZ.1
  have hP:∀i,1≤ input.P i:=by
    intro i
    change 1≤src.P i.val.val
    rw [hmatch.scale]
    exact Real.one_le_rpow hz.le (hw i.val.val)
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤N:=
    (child_card Bp.val).trans ((child_card B.val).trans hcard)
  have hmass:mass input≤mass src:=
    (child_mass (activeInput (child src C R0 B τ t)) ((Ideal.span {prime})^k) (R0*C) Bp υ v0).trans
      (child_mass src C R0 B τ t)
  have hsource:=hgZ.2 ⟨CenteredMomentCommonProfile.liveIndices B.val,CenteredMomentCommonProfile.liveIndices Bp.val⟩ input p
    (fun i=>hloSrc i.val.val) (fun i=>hhiSrc i.val.val) hP hp₁.symm hp₂.symm (mass src)
    hupperSrc hcardInput hb1 hb2 hb1max hb2max hmass
    ((R0*C)*(Ideal.span {prime})^k) seed hready.puncture_ne hseed hseed0 hseedcap hready.source_nonneg hready.source_cap
    hready.conductor_cap hready.puncture_cap
  change Scols=finiteColumns (Fintype.piFinset input.pools) at hScols
  change β=coefficient input ((R0*C)*(Ideal.span {prime})^k) seed at hβ
  dsimp only at hsource
  subst Scols β
  obtain ⟨family,hfamily,hbound⟩:=hsource
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm0 hml hm2 hwidth r hr1 hr2 hr3 hr4
  let Ec:=OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+errorRemoval prime Z k+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh))
  have hEc:0≤Ec:=OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient_nonneg
    Cc C₀ C₁ p T height (dc+degree+4*n) Z _ hCc.le hC₀ hC₁ hheight (zero_le_one.trans hz.le)
  have hpzero (j:Fin 2):p.profile j 0=0:=by
    by_contra hn
    exact (not_le_of_gt haPlain) ((p.support j hn).1)
  have hz1:input.W₁ 0=0:=by change src.W₁ 0=0;rw [←hp₁];exact hpzero 0
  have hz2:input.W₂ 0=0:=by change src.W₂ 0=0;rw [←hp₂];exact hpzero 1
  have hlowerInput:lower ≤ input.lower:=hlowerSrc
  have hplain₁:∀x,input.W₁ x≠0→a≤x:=by
    intro x hx
    change src.W₁ x≠0 at hx
    rw [←hp₁] at hx
    exact (p.support 0 hx).1
  have hplain₂:∀x,input.W₂ x≠0→a≤x:=by
    intro x hx
    change src.W₂ x≠0 at hx
    rw [←hp₂] at hx
    exact (p.support 1 hx).1
  have hlowerBeta (I:Ideal O)
      (hI:coefficient input ((R0*C)*(Ideal.span {prime})^k) seed I≠0):
      asource*volume input≤(I.absNorm:ℝ):=by
    exact (mul_le_mul_of_nonneg_right hasourceFactor (volume_pos input).le).trans
      (OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.actual_lower_support N lower a hlower haPlain
        input hcardInput hlowerInput hplain₁ hplain₂ _ seed I hI)
  apply hbound χ₀ m hm0 hml hm2 Km (nominal input Km) hready.scale_pos hready.volume_cap
    hready.nominal_cap (le_refl _) hready.frequency_pos hready.frequency_cap
    (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k))
    (mul_pos (mul_pos (zero_lt_one.trans_le hcost) (norm_pos τ.modulus τ.modulus_ne_bot))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _))
    Ec Ec hEc hEc ?_ ?_ r hr1 hr2 hr3 hr4
  all_goals
    intro q hq U dyad hphysical D0 hD0 hD0cap hD0sq χ v B₂ hB₂ alloc halloc
    have hqp:=q.property
    have hg:=actual_common_gates input ((R0*C)*(Ideal.span {prime})^k) seed hseed hz1 hz2 q.val.1 q.val.2 hqp
    have hs:=commonLabels_supported (activeSource _ _) _ _ q.property
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ v0 hυ input rfl
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.1 ((R0*C)*(Ideal.span {prime})^k) (Or.inl rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.1.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  · exact hm θ Z hZmZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hcard hlowerSrc hupperSrc C D R0 hC hD hCD E B τ t hB hmod
      K sigma delta reserve cost asource hK hsigma hcost hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ v0 hυ input rfl
      _ _ q.val.1 q.val.2 hs.1 hs.2 hg.2.2.1 U _ _ _ (fun i=>(dyad i:ℤ))
      hlowerBeta hphysical (family q U) (hfamily q U) χ (hwidth q hq U dyad hphysical χ)
      q.val.2 ((R0*C)*(Ideal.span {prime})^k) (Or.inr rfl) hready.puncture_ne hready.puncture_cap
      (hg.2.2.2.2.2.2.trans hready.source_cap) B₂ hB₂ D0 alloc p hp₁ hp₂
      hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip

end SevenEighths.CenteredMomentEnergyCanonicalErrorGaussian

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalErrorAdmitted. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorAdmitted

open OAI.SevenEighths.CenteredMomentEnergyCanonicalErrorAdmitted hiding actual_error_smaller_gaussian

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_error_smaller_gaussian
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve cost asource:ℝ,0<K → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input ((R0*C)*(Ideal.span {prime})^(k+1)) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let Echild:=OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient Cc C₀ C₁ p T height (dc+degree+4*n) Z
      ((Bcap+Bcap)*εmask+(εchild+εremove+errorRemoval prime Z (k+1)+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh))
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc v0
        εsrc (seed.absNorm:ℝ)
        (seededFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Kerror v0
          (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1))) Echild Echild r (∏i,input.lo i) a (seed.absNorm:ℝ)
          (dc+degree+4*n) (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalErrorGaussian.actual_error_gaussian_from_bands (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  let Zw:=OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth.threshold N upper sigma hupper hsigma
  refine ⟨Kc,hKc,max Zi Zw,lt_of_lt_of_le hZi (le_max_left _ _),?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  subst input
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  have hZiZ:Zi≤Z:=(le_max_left _ _).trans hZ
  have hZw:Zw≤Z:=(le_max_right _ _).trans hZ
  have hz:1<Z:=hZi.trans_le hZiZ
  have hk':k+1=1 ∨ k+1=6 ∨ k+1=7:=by omega
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZiZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K sigma delta reserve cost asource hK hsigma.le hcost hasource hdelta hreserve haSource
    prime hprime (k+1) hk' hprimeScale hslot Bp υ v0 hυ _ rfl
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip
    hcap hMdecl hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  apply hbound χ₀ m hm hml hm2 ?_ r hr1 hr2 hr3 hr4
  intro q hq U dyad hphysical χ
  have hs:=commonLabels_supported (activeSource Scols β) _ _ q.property
  have hη:(src.η.modulus.absNorm:ℝ)≤Z^(Real.logb Z (src.η.modulus.absNorm:ℝ)):=by
    rw [Real.rpow_logb (zero_lt_one.trans hz) (ne_of_gt hz)
      (norm_pos src.η.modulus src.η.modulus_ne_bot)]
  have hh:=OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth.error_child_width N upper sigma hupper hsigma
    Z hZw src hcard hupperSrc C D R0 hC hD hCD E B τ t hB hmod
    prime hprime k hk hslot Bp υ χerr v0 hN K delta reserve ξ
    (Real.logb Z (src.η.modulus.absNorm:ℝ)) Mwidth hK hdelta hreserve hξsmall hη hMwidth
    (activeSource Scols β) β q.val.1 q.val.2 hs.1 hs.2 U (family q U) (hfamily q U)
    _ CenteredMomentFirstAmplificationChoice.ballProfile (fun i=>(dyad i:ℤ)) hphysical χ
  exact hh.le.trans hdrop

end SevenEighths.CenteredMomentEnergyCanonicalErrorAdmitted

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalErrorPower. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorPower

open OAI.SevenEighths.CenteredMomentEnergyCanonicalErrorPower hiding actual_error_power_from_bands

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_error_power_from_bands
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve cost asource:ℝ,0<K → 1≤cost → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀Scols:Finset (Ideal O),∀β:Ideal O→ℂ,
    Scols=finiteColumns (Fintype.piFinset input.pools) →
    β=coefficient input ((R0*C)*(Ideal.span {prime})^(k+1)) seed →
    ∃family:(q:ActiveLabel Scols β)→Finset (CommonIndex q.val.1 q.val.2)→RayCharacter→Character,
      (∀q U,Family input.η q.val.1 q.val.2
        (commonLabels_supported (activeSource Scols β) _ _ q.property).1
        (commonLabels_supported (activeSource Scols β) _ _ q.property).2 U (family q U)) ∧
    ∀_χ₀:RayCharacter,∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n);
    let Hweights:=coefficients N upper (max 1 b) (max 1 b) (mass src) Sp p J
      (internalQ Q η₀) Kc v0 εsrc (seed.absNorm:ℝ)
      (OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients.fixedFactors Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap cost Ebase v0
        (OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
        (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile);
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,Hweights j*OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalErrorAdmitted.actual_error_smaller_gaussian (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  refine ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Kc,hKc,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  subst input
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0
  let Km:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input rfl
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β hScols hβ
  refine ⟨family,hfamily,?_⟩
  intro χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  have hg:=hbound χ₀ m hm hml hm2 r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  let Ebase:=Cc*(C₀+C₁)*diagonalControl CenteredMomentFirstAmplificationChoice.ballProfile*
      (p.control T)^2*(1+height)^(dc+degree+4*n)
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hE:0≤Ebase:=by dsimp [Ebase];have hd:=diagonalControl_nonneg CenteredMomentFirstAmplificationChoice.ballProfile;positivity
  have hcardInput:Fintype.card (CenteredMomentCommonProfile.liveIndices Bp.val)≤N:=
    (live_card_le Bp.val).trans ((live_card_le B.val).trans hcard)
  have hloProd:=OAI.SevenEighths.CenteredMomentEnergyOriginalProfileControl.lower_product input N lower hlower hcardInput
    (fun i=>hlowerSrc.trans (src.lower_le i.val.val))
  have hlo:OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a≤(∏i,input.lo i)*a*a:=by
    unfold OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor
    simpa only [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hloProd (sq_nonneg a)
  have hcoef:=OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients.error_coefficients
    N upper (max 1 b) (max 1 b) (mass src) Sp p J (internalQ Q η₀) Kc prime (k+1)
    Cm Ce Cd Ct Z εsrc δsrc θsrc Bcap saving Km v0 (τ.modulus.absNorm:ℝ) cost Ebase
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid r
    (∏i,input.lo i) a (OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a) (seed.absNorm:ℝ)
    (dc+degree+4*n) Sf CenteredMomentFirstAmplificationChoice.ballProfile
    (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
    (le_trans zero_le_one (le_max_left _ _)) hKc.le (Nat.cast_nonneg _) hCm.le hCe hz hE
    (by unfold Km errorCommonRadius;positivity)
    (OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain) hlo
  have hexp:
      (Bcap+Bcap)*εmask+(εchild+εremove+errorRemoval prime Z (k+1)+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          delta+reserve+θsource)/6+θclip/3+κ*mesh)=
      errorRemoval prime Z (k+1)+(Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)))/6+paid :=by
    dsimp [paid];ring
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  have hh:=mul_le_mul_of_nonneg_right (hcoef j)
    (Real.rpow_nonneg (volume_pos input).le (powers εsrc j))
  simpa only [OAI.SevenEighths.CenteredMomentEnergyChildEnvelopeFitting.coefficient,hexp,Ebase,paid] using hh

end SevenEighths.CenteredMomentEnergyCanonicalErrorPower

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalErrorHomogeneous. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyCanonicalErrorHomogeneous hiding actual_error_homogeneous

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_error_homogeneous
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i) → (∀i,src.hi i=highs i) →
    Fintype.card α≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|v0|+height)^Jheight*
        Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  obtain ⟨n,T,dc,Cc,hCc,J,Sp,Sf,hSp,Cm,Ce,Cd,Ct,hCm,hCe,hCd,hCt,hmain⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalErrorPower.actual_error_power_from_bands (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma hsigma hξsmall
  have hlo:=OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor_pos N lower a hlower haPlain
  obtain ⟨Uprofile,Jheight,hweights⟩:=
    OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.actual_weights (a:=a) (b:=b)
      N upper (max 1 b) (max 1 b) ((max 1 Mslot)^N)
      (OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a)
      Cm Ce Cd Ct Cc cost εsrc δsrc θsrc Bcap J (dc+degree+4*n) (dc+degree+4*n)
      Sp T Sf CenteredMomentFirstAmplificationChoice.ballProfile
      (zero_le_one.trans hupper) (le_trans zero_le_one (le_max_left _ _))
      (le_trans zero_le_one (le_max_left _ _)) (by positivity) hlo
      hCm.le hCe hCd.le hCt.le hCc.le (zero_le_one.trans hcost)
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Kc,hKc,Zi,hZi,hi⟩:=hmain η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,hwbound⟩:=hweights (internalQ Q η₀) Kc hKc.le
  refine ⟨Cbound,hCbound,Zi,hZi,?_⟩
  intro θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  let Scols:=finiteColumns (Fintype.piFinset input.pools)
  let β:=coefficient input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
  obtain ⟨family,hfamily,hbound⟩:=hi θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve cost asource hK hcost hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower Scols β rfl rfl
  have hg:=hbound 1 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hz:0<Z:=zero_lt_one.trans (hZi.trans_le hZ)
  have hmass:mass src≤(max 1 Mslot)^N:=
    OAI.SevenEighths.CenteredMomentEnergyOriginalProfileControl.slot_product_le src N (max 1 Mslot)
      (le_max_left _ _) hcard (fun i=>(hMs i).trans (le_max_right _ _))
  have hnseed:1≤(seed.absNorm:ℝ):=norm_ge_one seed hseed0
  have hh:=hwbound p Z v0 height (mass src) (seed.absNorm:ℝ) C₀ C₁
    hz hheight (mass_nonneg src) hmass hnseed hC₀ hC₁
  dsimp only at hh
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos input).le _)
  apply mul_le_mul_of_nonneg_right (hh j)
  fin_cases j <;> simp only [OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold errorCommonRadius
  all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalErrorHomogeneous

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalErrorSubsets. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalErrorSubsets

open OAI.SevenEighths.CenteredMomentEnergyCanonicalErrorSubsets hiding actual_original_subsets_error_power

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {α:Type*}[Fintype α][DecidableEq α]

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstNestedSeededGaussianPower CenteredMomentFirstSecondInputGates

theorem actual_original_subsets_error_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|v0|+height)^Jheight*
        Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  have hmain (Aorig:Finset α):=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalErrorHomogeneous.actual_error_homogeneous (α:=Aorig) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource (fun i=>lows i.val) (fun i=>highs i.val)
      (fun i=>hhighs i.val) εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  choose Uj Jj hj using hmain
  let Uprofile:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Jheight:ℕ:=∑Aorig:Finset α,Jj Aorig
  refine ⟨Uprofile,Jheight,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  choose Cj hCj Zj hZj hconsume using fun Aorig=>hj Aorig η₀ Q hQM hQ0 hQt hQ72
  let Cbound:ℝ:=1+∑Aorig:Finset α,Cj Aorig
  let Z₀:ℝ:=2+∑Aorig:Finset α,|Zj Aorig|
  have hCbound:0<Cbound:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>(hCj Aorig).le)
    dsimp [Cbound];linarith
  have hZ₀:1<Z₀:=by
    have hh:=Finset.sum_nonneg (fun Aorig (_:Aorig∈(Finset.univ:Finset (Finset α)))=>abs_nonneg (Zj Aorig))
    dsimp [Z₀];linarith
  have hCC (Aorig:Finset α):Cj Aorig≤Cbound:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>(hCj A).le)
      (Finset.mem_univ Aorig)
    dsimp [Cbound];linarith
  have hZZ (Aorig:Finset α):Zj Aorig≤Z₀:=by
    have hh:=Finset.single_le_sum (fun A (_:A∈(Finset.univ:Finset (Finset α)))=>abs_nonneg (Zj A))
      (Finset.mem_univ Aorig)
    dsimp [Z₀];linarith [le_abs_self (Zj Aorig)]
  refine ⟨Cbound,hCbound,Z₀,hZ₀,?_⟩
  intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
  dsimp only
  intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  have hposA:=positiveAt_subtype M H hH Aorig Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
    Mcap εchild κ Z η₀ Q degree S C₁ hpos
  have hg:=hconsume Aorig θ Z ((hZZ Aorig).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hposA
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve asource hK hasource hdelta hreserve haSource
    prime hprime k hk hprimeScale hslot Bp υ χerr v0 hN hυ input hinput
    hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
  dsimp only at hg ⊢
  have hsub:Uj Aorig⊆Uprofile:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨Aorig,Finset.mem_univ _,hx⟩
  have hp:p.control (Uj Aorig)≤p.control Uprofile:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hJ:Jj Aorig≤Jheight:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ Aorig)
  have hz:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hp0:=p.control_nonneg (Uj Aorig)
  have hp1:=p.control_nonneg Uprofile
  have hh:(1+|v0|+height)^(Jj Aorig)≤(1+|v0|+height)^Jheight:=
    pow_le_pow_right₀ (by linarith [abs_nonneg v0]) hJ
  have hfront:Cj Aorig*(C₀+C₁+1)*(p.control (Uj Aorig))^2*(1+|v0|+height)^(Jj Aorig)≤
      Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|v0|+height)^Jheight:=by
    have hc:=hCC Aorig
    have hc0:0≤Cj Aorig:=(hCj Aorig).le
    gcongr
  apply hg.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
  apply mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
  fin_cases j <;> simp only [OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
    try unfold errorCommonRadius
  all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalErrorSubsets

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalAmplifiedUniform. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

theorem actual_original_subsets_amplified_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bcap Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hBcap:0≤Bcap)(hξ:0<ξ)
    (sigma cost:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(hcost:1≤cost):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧
    (∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    let input:=child src C R0 B τ t
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve
    Ready input (R0*C) Kmain Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input (R0*C) seed CenteredMomentFirstAmplificationChoice.ballProfile Kmain≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2) ∧
    (∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K delta reserve asource:ℝ,0<K → 0<asource →
    0≤delta → 0≤reserve → a0≤asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ t →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime (k+1)
    Ready input ((R0*C)*(Ideal.span {prime})^(k+1)) Kerror Z ξ Bcap →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    asource≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    ∀r:ℝ,Z^r≤ input.X₁ → Z^r≤ input.X₂ → Z^r≤ input.Y₁ → Z^r≤ input.Y₂ →
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    normalizedGaussSource input ((R0*C)*(Ideal.span {prime})^(k+1)) seed
      CenteredMomentFirstAmplificationChoice.ballProfile Kerror≤
      (∑j,(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
        Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ))*
        OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients.errorPowers prime (k+1)
        (τ.modulus.absNorm:ℝ) Z Kerror
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))) paid saving r j*
        (volume input)^(powers εsrc j))*mass input^2) :=by
  obtain ⟨Um,Jm,hm⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalMainSubsets.actual_original_subsets_main_power (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  obtain ⟨Ue,Je,he⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalErrorSubsets.actual_original_subsets_error_power (α:=α) M H hH
      Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
      L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
      hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
      hεsrc hδsrc hθsrc hBcap hξ sigma cost hsigma hξsmall hcost
  refine ⟨Um∪Ue,max Jm Je,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cm,hCm,Zm,hZm,hmain⟩:=hm η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ce,hCe,Ze,hZe,herror⟩:=he η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cm+Ce,add_pos hCm hCe,max Zm Ze,lt_of_lt_of_le hZm (le_max_left _ _),?_,?_⟩
  ·
    intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
      hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
      hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
    dsimp only
    intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hg:=hmain Aorig θ Z ((le_max_left _ _).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hfront:=front_mono p Um (Um∪Ue) Finset.subset_union_left Jm (max Jm Je) (le_max_left _ _)
      Cm (Cm+Ce) C₀ C₁ t height hCm.le (le_add_of_nonneg_right hCe.le) hC₀ hC₁ hheight
    dsimp only at hg ⊢
    have hz:0<Z:=zero_lt_one.trans ((lt_of_lt_of_le hZm (le_max_left Zm Ze)).trans_le hZ)
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
    apply mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
    fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
      try unfold mainCommonRadius
    all_goals positivity
  ·
    intro Aorig θ Z hZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hwL
      hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
      hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ χerr hN hυ input hinput
    dsimp only
    intro hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hg:=herror Aorig θ Z ((le_max_right _ _).trans hZ) εchild C₀ C₁ hC₀ hC₁ hzero hpos
      w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
      hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
      K delta reserve asource hK hasource hdelta hreserve haSource
      prime hprime k hk hprimeScale hslot Bp υ χerr t hN hυ input hinput
      hready seed hseed hseed0 hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
      hcap hMdecl hMwidth hdrop hclip hsourceLower r hr1 hr2 hr3 hr4
    have hfront:=front_mono p Ue (Um∪Ue) Finset.subset_union_right Je (max Jm Je) (le_max_right _ _)
      Ce (Cm+Ce) C₀ C₁ t height hCe.le (le_add_of_nonneg_left hCm.le) hC₀ hC₁ hheight
    dsimp only at hg ⊢
    have hz:0<Z:=zero_lt_one.trans ((lt_of_lt_of_le hZm (le_max_left Zm Ze)).trans_le hZ)
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (volume_pos _).le _)
    apply mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg hz.le _)) (Nat.cast_nonneg _))
    fin_cases j <;> simp only [OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients.errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;>
      try unfold errorCommonRadius
    all_goals positivity

end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalAnnularPower. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalAnnularPower

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower hiding actual_original_subsets_annular_power

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power

open OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

open OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum

open OAI.SevenEighths.CenteredMomentFirstReferenceSource

open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily

open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility

open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows

open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice

open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

theorem actual_original_subsets_annular_power
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(_hξ1:ξ≤1)(hreserve:0<reserve):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3));
    P.Nonempty ∧ Z^(sigma/3-primeLoss)≤(P.card:ℝ) ∧
    ∀τ:Character,∃υ:(Aorig:Finset α)→(Ac:Finset Aorig)→elementPool P→Fin 3→RayCharacter→Character,
    (∀Aorig Ac prime i χ,(υ Aorig Ac prime i χ).modulus.absNorm≤
      radicalBound (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime.val
        (errorMovingExponent (errorIndex i))) ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → (C.absNorm:ℝ)≤Z^(A+1) →
    ∀E:Finset (CommonIndex C D),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K H0:ℝ,0<K → 0<H0 →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)) Z ξ →
    8*H0≤Z^(amplifierCap A 0 ξ) →
    ∀(B:actualAllocations src.pools C)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) →
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap)) →
    let input:=child src C R0 B τ t;
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ);
    let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve;
    let Hcoef:=fun j=>Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+|t|+height)^Jheight*
      Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ);
    let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j;
    let aerror:=fun (prime:elementPool P)(i:Fin 3)(_χ:RayCharacter)(j:Fin 4)=>
      Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
        (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))
        deficit paid saving (rmain-errorRemoval prime Z (errorIndex i+1)) j;
    childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile
      H0≤
      (∑j,sourceCoefficients P ((amplifierCap A 0 ξ+2*sigma)/(sigma/6)) amain aerror (powers εsrc) j*
        (volume input)^(powers εsrc j))*mass input^2 :=by
  let Bcap:=readyBudget A Pcap
  have hBcap:0≤Bcap:=readyBudget_nonneg A Pcap hA hPcap
  have hAmp:0≤amplifierCap A 0 ξ:=by unfold amplifierCap;positivity
  obtain ⟨U,J,huniform⟩:=actual_original_subsets_amplified_power (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bcap Bseed ξ saving
    hεsrc hδsrc hθsrc hBcap hξ sigma referenceCost hsigma hξsmall referenceCost_ge_one
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cbound,hCbound,Zbase,hZbase,hm,he⟩:=huniform η₀ Q hQM hQ0 hQt hQ72
  have hall:=Filter.eventually_all.mpr (fun Aorig:Finset α=>
    eventually_original_subsets_power_amplification (Ω:=Aorig) M H hH fixedBadPrimes (Finset.Subset.refl _)
      sigma primeLoss (Pcap+A+1) Bseed (amplifierCap A 0 ξ) (max 1 bslot) eta 1 ξ reserve
      hsigma hPrimeLoss hAmp (by positivity) heta (by norm_num) hξ.le hreserve)
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss hAmp heta
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.mp
    (hall.and (hsepEvent.and (eventually_ge_atTop Zbase)))
  refine ⟨Cbound,hCbound,max Z₀ Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Z hZthreshold
  obtain ⟨hamp,hsepdata,hZZbase⟩:=
    hZ₀ Z ((le_max_left _ _).trans hZthreshold)
  have hZ:1<Z:=hZbase.trans_le hZZbase
  dsimp only
  have hbase:=hamp (∅:Finset α)
  refine ⟨hbase.2.1,hbase.2.2.1,?_⟩
  intro τ
  have hf (Aorig:Finset α):=(hamp Aorig).2.2.2 τ
  choose υ hυN henergy using hf
  refine ⟨υ,hυN,?_⟩
  intro Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC
    E hmod K H0 hK hH0 houter hHcap B t hB seed hseed hseedne hseedcap
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth
    hdrop hclip hsourceLower hreadym herrorPacket
  let input:=child src C R0 B τ t
  let delta:=frequencyLoss Z 32 ξ
  have hdelta:0≤delta:=frequencyLoss_nonneg Z 32 ξ hZ (by norm_num) hξ.le
  have hRC:(R0*C).absNorm=R0.absNorm*C.absNorm:=map_mul _ _ _
  have hRcommon:( (R0*C).absNorm:ℝ)≤Z^(Pcap+A+1):=by
    rw [hRC,Nat.cast_mul]
    calc
      _≤Z^Pcap*Z^(A+1):=mul_le_mul hRcap hNC (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)
      _=Z^(Pcap+A+1):=by rw [←Real.rpow_add (by linarith:0<Z)];congr 1;ring
  have hmainlower:=main_minimum_lower src C R0 hC.1 B τ t Z hZ
  have hmain:=hm Aorig θ Z hZZbase εchild C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
    K delta reserve a0 hK ha0 hdelta hreserve.le le_rfl
    hreadym seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
    hcap hMdecl hMwidth hdrop hclip hsourceLower _
    hmainlower.1 hmainlower.2.1 hmainlower.2.2.1 hmainlower.2.2.2
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Hcoef:=fun j=>Cbound*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J*
    Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool (primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))))
    (i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>Hcoef j*
      errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))
      deficit paid saving (rmain-errorRemoval prime Z (errorIndex i+1)) j
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have haerror:∀prime i χ j,0≤aerror prime i χ j:=by
    intro prime i χ j
    apply mul_nonneg (hHcoef j)
    fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk]
    all_goals try unfold errorRadius errorCommonRadius
    all_goals positivity
  have hsupp:∀i,Function.support (input.W i)⊆Set.Iic (max 1 bslot):=by
    intro i x hx
    exact ((src.support i.val hx).2.trans (hhi i.val)).trans (le_max_right _ _)
  let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun i=>w i.val
  have hz:∀i,z i≤eta:=fun i=>hweta i.val
  have hlen:∀i,input.P i=Z^(z i):=fun i=>hmatch.scale i.val
  obtain ⟨_,_,_,hsep,hdata,_⟩:=hsepdata
  have herror:∀prime:elementPool (primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))),
      ∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput input).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      childNormalizedGaussSource (activeInput input) ((Ideal.span {prime.val})^(errorIndex i+1))
        (R0*C) seed Bp (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t
        CenteredMomentFirstAmplificationChoice.ballProfile
        (errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1))≤
      (∑j,aerror prime i χ j*(volume (child (activeInput input)
        ((Ideal.span {prime.val})^(errorIndex i+1)) (R0*C) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t))^(powers εsrc j))*
        mass (child (activeInput input) ((Ideal.span {prime.val})^(errorIndex i+1)) (R0*C) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) input.t)^2:=by
    intro prime i χ Bp
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    have hprime:prime.val≠0:=hd.1.ne_zero
    have hcop:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact CenteredMomentFirstAmplificationChoice.original_slot_coprime (original input (R0*C) seed).active
        Z sigma (max 1 bslot) eta hZ.le (by positivity) hsep z hz hlen hsupp
        (original input (R0*C) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*C) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=CenteredMomentFirstAmplificationChoice.errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυN Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have hvcap:=actual_error_reference_cap τ _ χ prime.val hprime (errorIndex i) hk Z hZ hN
    have hre:=herrorPacket prime i χ Bp
    rcases hre with hdead|hlive
    · change normalizedGaussSource _ _ _ _ _≤_
      apply (CenteredMomentFirstSecondInputGates.normalized_zero _ _ _ hdead _ _).le.trans
      exact mul_nonneg (Finset.sum_nonneg (fun j _=>mul_nonneg (haerror prime i χ j)
        (Real.rpow_nonneg (volume_pos _).le _))) (sq_nonneg _)
    · have hlower:=error_minimum_lower src C R0 hC.1 B τ t prime.val hprime
        (errorIndex i+1) Bp (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t Z hZ
      have hprimeScale: sigma/6≤Real.logb Z (normValue prime.val):=by
        have hh:=Real.logb_le_logb_of_le hZ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/6)) (hdata _ hd.2.1).2.2.1
        simpa only [normValue,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
      have hh:=he Aorig θ Z hZZbase εchild C₀ C₁ hC₀ hC₁ hzero hpos
        w σ freq height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
        hloSrc hhiSrc hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD E B τ t hB hmod
        K delta reserve a0 hK ha0 hdelta hreserve.le le_rfl
        prime.val hprime (errorIndex i) hk hprimeScale hcop Bp _ χ hN hvcap _ rfl
        hlive seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip
        hcap hMdecl hMwidth hdrop hclip hsourceLower _
        hlower.1 hlower.2.1 hlower.2.2.1 hlower.2.2.2
      exact hh
  have hE:Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}≠0:=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hann:=henergy Aorig (CenteredMomentCommonProfile.liveIndices B.val) input rfl hsupp z hz hlen
    (R0*C) seed (mul_ne_zero hR0 hC.1) hseedne hRcommon hseedcap
    (Real.logb Z (D.absNorm:ℝ)) (Real.logb Z (C.absNorm:ℝ)) C D
    (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) hE K (volume src) _
    hK (volume_pos src) (by simp only [one_mul];exact le_rfl) H0 hH0 houter hHcap
    amain aerror (powers εsrc) haerror (by simpa only [mul_one,nominalLog,input,amain,Hcoef,Kmain,mainRadius,paid,deficit,rmain,delta] using hmain)
    (by simpa only [mul_one,nominalLog,errorRadius,delta] using herror)
  apply hann.trans_eq
  rw [source_coefficients_identity _ _ _ (volume_pos input).le]
  dsimp only [normValue]
  ring

end SevenEighths.CenteredMomentEnergyCanonicalAnnularPower

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalLowColumn. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLowColumn

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn hiding actual_admitted_subsets_low_column

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power

open OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

open OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum

open OAI.SevenEighths.CenteredMomentFirstReferenceSource

open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily

open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility

open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows

open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice

open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower hiding actual_original_subsets_annular_power

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower

open OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

theorem actual_admitted_subsets_low_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)(heps1:εsrc≤1):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3));
    P.Nonempty ∧ Z^(sigma/3-primeLoss)≤(P.card:ℝ) ∧
    ∀τ:Character,∃υ:(Aorig:Finset α)→(Ac:Finset Aorig)→elementPool P→Fin 3→RayCharacter→Character,
    (∀Aorig Ac prime i χ,(υ Aorig Ac prime i χ).modulus.absNorm≤
      radicalBound (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime.val
        (errorMovingExponent (errorIndex i))) ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → (C.absNorm:ℝ)≤Z^(A+1) →
    ∀E:Finset (CommonIndex C D),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K H0:ℝ,0<K → 0<H0 →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)) Z ξ →
    8*H0≤Z^(amplifierCap A 0 ξ) →
    ∀(t:ℝ)(seed0:Ideal O),seed0∣C →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → 0≤Mdecl → Mdecl≤A →
    Real.logb Z (volume src)≤5*Mdecl/6 →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    (∀B:actualAllocations src.pools C,
      frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) ∧
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap))) →
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance C D Z);
    (commonEnergy (original src R0 seed0) C hC τ t seed
      CenteredMomentFirstAnnularMajorant.profile H0).re≤
      (ref/(seed.absNorm:ℝ))*(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hann⟩:=actual_original_subsets_annular_power (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve
  obtain ⟨Cb,hCb,hcommon⟩:=common_energy_reference_powers N lower upper εsrc hlower hupper hεsrc
  let Mamp:=amplifierCap A 0 ξ
  let avg:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card RayCharacter:ℝ))
  have hMamp:0≤Mamp:=by dsimp [Mamp,amplifierCap];positivity
  have havg:0<avg:=by dsimp [avg];positivity
  have hmcap:0<(max 1 Mslot)^(2*N):=pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ca,hCa,Z₀,hZ₀,hannZ⟩:=hann η₀ Q hQM hQ0 hQt hQ72
  let Ccolumn:=Cb*upper^N*avg*Ca*(max 1 Mslot)^(2*N)
  have hCcolumn:0<Ccolumn:=by dsimp [Ccolumn];positivity
  refine ⟨Ccolumn,hCcolumn,Z₀,hZ₀,?_⟩
  intro Z hZZ
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hZpos:0<Z:=zero_lt_one.trans hZ
  obtain ⟨hPne,hPcard,hfamily⟩:=hannZ Z hZZ
  dsimp only at hPne hPcard hfamily ⊢
  refine ⟨hPne,hPcard,?_⟩
  intro τ
  obtain ⟨υ,hυ,henergy⟩:=hfamily τ
  refine ⟨υ,hυ,?_⟩
  intro Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
    K H0 hK hH0 houter hHcap t seed0 hseed0 seed hseed hseedne hseedcap
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hlow
    hcap hMdecl hMwidth hdrop hclip hsourceLower hpackets
  let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))
  let delta:=frequencyLoss Z 32 ξ
  let Bcap:=readyBudget A Pcap
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=parentLower src Z-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Kerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1)
  let rerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    rmain-errorRemoval prime Z (errorIndex i+1)
  let front:=Ca*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J
  let Hcoef:=fun j:Fin 4=>front*
    Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool P)(i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>
    Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror prime i χ) deficit paid saving (rerror prime i χ) j
  let coeff:=sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror (powers εsrc)
  have hNseed:0<(seed.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hseedne
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hfront:0≤front:=by dsimp [front];positivity
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have hKmain:0≤Kmain:=by unfold Kmain mainRadius mainCommonRadius;positivity
  have hKerror:∀prime i χ,0≤Kerror prime i χ:=by
    intro prime i χ;unfold Kerror errorRadius errorCommonRadius;positivity
  have hcoeff:∀j,0≤coeff j:=source_coefficients_nonneg P _ (by positivity)
    amain aerror (powers εsrc)
    (fun j=>mul_nonneg (hHcoef j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZpos.le hKmain j))
    (fun prime i χ j=>mul_nonneg (hHcoef j)
      (error_coefficients_nonneg _ _ _ _ _ _ _ _ _ hq.le hZpos.le (hKerror prime i χ) j))
  have hchildren (B:actualAllocations src.pools C)
      (hB:frozenCoefficient B.val C R0 src.ν src.W src.P≠0):
      childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,coeff j*(volume (child src C R0 B τ t))^(powers εsrc j))*mass (child src C R0 B τ t)^2:=by
    exact henergy Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
      hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
      hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
      K H0 hK hH0 houter hHcap B t hB seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
      Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
      (hpackets B hB).1 (hpackets B hB).2
  have hcommonBound:=hcommon src hcard hlowerSrc hupperSrc C R0 seed0 hC hseed0 τ t seed
    CenteredMomentFirstAnnularMajorant.profile H0 Z (OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance C D Z)
    hH0 hZpos (fun z=>CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 coeff (powers εsrc)
    hcoeff (powers_nonneg εsrc hεsrc.le) hchildren
  have hscalar:=actual_low_homogeneous_four_powers M H fixedBadPrimes (Finset.Subset.refl _)
    src.η τ C D hC hD hCD E K (volume src) Z sigma delta reserve paid εsrc saving Mdecl A Mamp primeLoss
    hK (volume_pos src) hZ hsigma hεsrc.le hMdecl0 hMA hMdecl hlow hPrimeLoss.le hMamp hPcard hmod
    upper N hupper Hcoef hHcoef front (seed.absNorm:ℝ) (A+1)
    (OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap)
    hfront hNseed heps1 hNC (fun j=>le_rfl) rmain rerror
  dsimp only at hscalar
  have hmass:=source_mass_cap src N Mslot hcard hMs
  have hmass2:mass src^2≤(max 1 Mslot)^(2*N):=by
    calc
      _≤((max 1 Mslot)^N)^2:=pow_le_pow_left₀ (mass_nonneg src) hmass 2
      _=_:=by rw [←pow_mul];congr 1;omega
  have hheightSplit:=inherited_height_split t height J hheight
  let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*
    Z^(OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance C D Z)
  have href:0≤ref:=by dsimp [ref];positivity
  have hsum:0≤∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
      lossVector sigma delta reserve paid εsrc A saving j):=Finset.sum_nonneg (fun _ _=>Real.rpow_nonneg hZpos.le _)
  calc
    _≤ref*(Cb*mass src^2*∑j,normalizedPower upper (volume src) (C.absNorm:ℝ)
        (τ.modulus.absNorm:ℝ) Z (OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance C D Z)
        εsrc (coeff j) N (powers εsrc j)):=hcommonBound
    _≤ref*(Cb*mass src^2*((upper^N*avg*front/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul_of_nonneg_left hscalar
      exact mul_nonneg hCb.le (sq_nonneg _)
    _≤ref*(Cb*(max 1 Mslot)^(2*N)*((upper^N*avg*
        (Ca*(C₀+C₁+1)*(p.control U)^2*((1+height)^J*(1+|t|)^(2*J)))/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      have hfrontBound:front≤Ca*(C₀+C₁+1)*(p.control U)^2*
          ((1+height)^J*(1+|t|)^(2*J)):=
        mul_le_mul_of_nonneg_left hheightSplit
          (mul_nonneg (mul_nonneg hCa.le
            (add_nonneg (add_nonneg hC₀ hC₁) zero_le_one)) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hmass2 hCb.le
      · apply mul_le_mul_of_nonneg_right _ hsum
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
        apply div_le_div_of_nonneg_right _ hNseed.le
        exact mul_le_mul_of_nonneg_left hfrontBound
          (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le)
      · exact mul_nonneg (mul_nonneg
          (div_nonneg (mul_nonneg
            (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le) hfront) hNseed.le)
          (Real.rpow_nonneg hZpos.le _)) hsum
      · exact mul_nonneg hCb.le hmcap.le
    _=_:=by dsimp only [Ccolumn,ref,deficit,paid,Bcap,delta];ring

end SevenEighths.CenteredMomentEnergyCanonicalLowColumn

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalHighColumn. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalHighColumn

open OAI.SevenEighths.CenteredMomentEnergyCanonicalHighColumn hiding actual_admitted_subsets_high_column

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power

open OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

open OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum

open OAI.SevenEighths.CenteredMomentFirstReferenceSource

open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily

open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility

open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows

open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice

open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower hiding actual_original_subsets_annular_power

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower

open OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLowColumn OAI.SevenEighths.CenteredMomentEnergyCanonicalAnnularLower

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn hiding actual_admitted_subsets_low_column

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAnnularLower

open OAI.SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers

open OAI.SevenEighths.CenteredMomentEnergyFirstHighGaussianUniformPowers

theorem actual_admitted_subsets_high_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)(heps1:εsrc≤1):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cbound:ℝ,0<Cbound ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z →
    let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3));
    P.Nonempty ∧ Z^(sigma/3-primeLoss)≤(P.card:ℝ) ∧
    ∀τ:Character,∃υ:(Aorig:Finset α)→(Ac:Finset Aorig)→elementPool P→Fin 3→RayCharacter→Character,
    (∀Aorig Ac prime i χ,(υ Aorig Ac prime i χ).modulus.absNorm≤
      radicalBound (CenteredMomentChildRows.childCharacter τ χ) fixedBadMask prime.val
        (errorMovingExponent (errorIndex i))) ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(C D R0:Ideal O),∀hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → (C.absNorm:ℝ)≤Z^(A+1) →
    ∀E:Finset (CommonIndex C D),
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D} →
    ∀K H0:ℝ,0<K → 0<H0 →
    H0≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src)) Z ξ →
    8*H0≤Z^(amplifierCap A 0 ξ) →
    ∀(t:ℝ)(seed0:Ideal O),seed0∣C →
    ∀seed:Ideal O,Squarefree seed → seed≠0 → (seed.absNorm:ℝ)≤Z^Bseed →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → 0≤Mdecl → Mdecl≤A →
    Mwidth≤Mdecl →
    Z^(Mwidth/4)≤src.X₁ → Z^(Mwidth/4)≤src.X₂ →
    Z^(Mwidth/4)≤src.Y₁ → Z^(Mwidth/4)≤src.Y₂ →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    (∀B:actualAllocations src.pools C,
      frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
      Ready (child src C R0 B τ t) (R0*C)
      (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve) Z ξ (readyBudget A Pcap) ∧
    (∀prime:elementPool P,∀i:Fin 3,∀χ:RayCharacter,
      ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime.val})^(errorIndex i+1)),
      let d:=errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
        (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t;
      (∀I:Ideal O,coefficient d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1)) seed I=0) ∨
      Ready d ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
        (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z 32 ξ) reserve prime (errorIndex i+1))
        Z ξ (readyBudget A Pcap))) →
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance C D Z);
    (commonEnergy (original src R0 seed0) C hC τ t seed
      CenteredMomentFirstAnnularMajorant.profile H0).re≤
      (ref/(seed.absNorm:ℝ))*(Cbound*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hann⟩:=actual_original_subsets_annular_power (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve
  obtain ⟨Cb,hCb,hcommon⟩:=common_energy_reference_powers N lower upper εsrc hlower hupper hεsrc
  let Mamp:=amplifierCap A 0 ξ
  let avg:=56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card RayCharacter:ℝ))
  have hMamp:0≤Mamp:=by dsimp [Mamp,amplifierCap];positivity
  have havg:0<avg:=by dsimp [avg];positivity
  have hmcap:0<(max 1 Mslot)^(2*N):=pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ca,hCa,Z₀,hZ₀,hannZ⟩:=hann η₀ Q hQM hQ0 hQt hQ72
  let Ccolumn:=Cb*upper^N*avg*Ca*(max 1 Mslot)^(2*N)
  have hCcolumn:0<Ccolumn:=by dsimp [Ccolumn];positivity
  refine ⟨Ccolumn,hCcolumn,Z₀,hZ₀,?_⟩
  intro Z hZZ
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hZpos:0<Z:=zero_lt_one.trans hZ
  obtain ⟨hPne,hPcard,hfamily⟩:=hannZ Z hZZ
  dsimp only at hPne hPcard hfamily ⊢
  refine ⟨hPne,hPcard,?_⟩
  intro τ
  obtain ⟨υ,hυ,henergy⟩:=hfamily τ
  refine ⟨υ,hυ,?_⟩
  intro Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
    K H0 hK hH0 houter hHcap t seed0 hseed0 seed hseed hseedne hseedcap
    p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂
    hcap hMdecl hMwidth hdrop hclip hsourceLower hpackets
  let P:=primePool M H fixedBadPrimes (1/2) 1 (Z^(sigma/3))
  let delta:=frequencyLoss Z 32 ξ
  let Bcap:=readyBudget A Pcap
  let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let rmain:=Mwidth/4-Real.logb Z (C.absNorm:ℝ)
  let Kmain:=mainRadius C D E K (volume src) Z sigma delta reserve
  let Kerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    errorRadius C D E K (volume src) Z sigma delta reserve prime (errorIndex i+1)
  let rerror:=fun (prime:elementPool P)(i:Fin 3)(_:RayCharacter)=>
    rmain-errorRemoval prime Z (errorIndex i+1)
  let front:=Ca*(C₀+C₁+1)*(p.control U)^2*(1+|t|+height)^J
  let Hcoef:=fun j:Fin 4=>front*
    Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j)/(seed.absNorm:ℝ)
  let amain:=fun j=>Hcoef j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3) deficit paid saving rmain j
  let aerror:=fun (prime:elementPool P)(i:Fin 3)(χ:RayCharacter)(j:Fin 4)=>
    Hcoef j*errorPowers prime (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror prime i χ) deficit paid saving (rerror prime i χ) j
  let coeff:=sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror (powers εsrc)
  have hNseed:0<(seed.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hseedne
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hfront:0≤front:=by dsimp [front];positivity
  have hHcoef:∀j,0≤Hcoef j:=by intro j;dsimp [Hcoef];positivity
  have hKmain:0≤Kmain:=by unfold Kmain mainRadius mainCommonRadius;positivity
  have hKerror:∀prime i χ,0≤Kerror prime i χ:=by
    intro prime i χ;unfold Kerror errorRadius errorCommonRadius;positivity
  have hcoeff:∀j,0≤coeff j:=source_coefficients_nonneg P _ (by positivity)
    amain aerror (powers εsrc)
    (fun j=>mul_nonneg (hHcoef j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZpos.le hKmain j))
    (fun prime i χ j=>mul_nonneg (hHcoef j)
      (error_coefficients_nonneg _ _ _ _ _ _ _ _ _ hq.le hZpos.le (hKerror prime i χ) j))
  have hchildren (B:actualAllocations src.pools C)
      (hB:frozenCoefficient B.val C R0 src.ν src.W src.P≠0):
      childNormalizedGaussSource src C R0 seed B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,coeff j*(volume (child src C R0 B τ t))^(powers εsrc j))*mass (child src C R0 B τ t)^2:=by
    have hann:=henergy Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
      hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
      hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
      K H0 hK hH0 houter hHcap B t hB seed hseed hseedne hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
      Mdecl Mwidth θclip hθclip hcap hMdecl hMwidth hdrop hclip hsourceLower
      (hpackets B hB).1 (hpackets B hB).2
    apply hann.trans
    exact actual_high_annular_sum src P C D R0 E B τ t
      K Z sigma delta reserve Mamp deficit paid saving Mwidth εsrc hZ hsigma hMamp
      hrawX₁ hrawX₂ hrawY₁ hrawY₂ Hcoef hHcoef
  have hcommonBound:=hcommon src hcard hlowerSrc hupperSrc C R0 seed0 hC hseed0 τ t seed
    CenteredMomentFirstAnnularMajorant.profile H0 Z (OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance C D Z)
    hH0 hZpos (fun z=>CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 coeff (powers εsrc)
    hcoeff (powers_nonneg εsrc hεsrc.le) hchildren
  have hPsrc:∀i,1≤src.P i:=by
    intro i
    rw [hmatch.scale i]
    exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i
    rw [hmatch.scale i,Real.logb_rpow hZpos hZ.ne']
  have hVcap:=OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity.original_volume_cap src Z κ Mdecl hZ hκsmall hPsrc
    (by simpa only [hlogs] using hcap)
  have hvolume:Real.logb Z (volume src)≤Mdecl:=by
    have hh:=Real.logb_le_logb_of_le hZ (volume_pos src) hVcap
    simpa only [Real.logb_rpow hZpos hZ.ne'] using hh
  have hscalar:=actual_high_homogeneous_four_powers M H fixedBadPrimes (Finset.Subset.refl _)
    src.η τ C D hC hD hCD E K (volume src) Z sigma delta reserve paid εsrc saving Mdecl Mwidth A Mamp primeLoss
    hK (volume_pos src) hZ hsigma hεsrc.le hMdecl0 hMA hMwidth hwidthle hvolume hPrimeLoss.le hMamp hPcard hmod
    upper N hupper Hcoef hHcoef front (seed.absNorm:ℝ) (A+1)
    (OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap)
    hfront hNseed heps1 hNC (fun j=>le_rfl)
  dsimp only at hscalar
  have hmass:=source_mass_cap src N Mslot hcard hMs
  have hmass2:mass src^2≤(max 1 Mslot)^(2*N):=by
    calc
      _≤((max 1 Mslot)^N)^2:=pow_le_pow_left₀ (mass_nonneg src) hmass 2
      _=_:=by rw [←pow_mul];congr 1;omega
  have hheightSplit:=inherited_height_split t height J hheight
  let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*
    Z^(OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance C D Z)
  have href:0≤ref:=by dsimp [ref];positivity
  have hsum:0≤∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
      lossVector sigma delta reserve paid εsrc A saving j):=Finset.sum_nonneg (fun _ _=>Real.rpow_nonneg hZpos.le _)
  calc
    _≤ref*(Cb*mass src^2*∑j,normalizedPower upper (volume src) (C.absNorm:ℝ)
        (τ.modulus.absNorm:ℝ) Z (OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance C D Z)
        εsrc (coeff j) N (powers εsrc j)):=hcommonBound
    _≤ref*(Cb*mass src^2*((upper^N*avg*front/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul_of_nonneg_left hscalar
      exact mul_nonneg hCb.le (sq_nonneg _)
    _≤ref*(Cb*(max 1 Mslot)^(2*N)*((upper^N*avg*
        (Ca*(C₀+C₁+1)*(p.control U)^2*((1+height)^J*(1+|t|)^(2*J)))/(seed.absNorm:ℝ))*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))):=by
      have hfrontBound:front≤Ca*(C₀+C₁+1)*(p.control U)^2*
          ((1+height)^J*(1+|t|)^(2*J)):=
        mul_le_mul_of_nonneg_left hheightSplit
          (mul_nonneg (mul_nonneg hCa.le
            (add_nonneg (add_nonneg hC₀ hC₁) zero_le_one)) (sq_nonneg _))
      apply mul_le_mul_of_nonneg_left _ href
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hmass2 hCb.le
      · apply mul_le_mul_of_nonneg_right _ hsum
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
        apply div_le_div_of_nonneg_right _ hNseed.le
        exact mul_le_mul_of_nonneg_left hfrontBound
          (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le)
      · exact mul_nonneg (mul_nonneg
          (div_nonneg (mul_nonneg
            (mul_nonneg (pow_nonneg (zero_le_one.trans hupper) _) havg.le) hfront) hNseed.le)
          (Real.rpow_nonneg hZpos.le _)) hsum
      · exact mul_nonneg hCb.le hmcap.le
    _=_:=by dsimp only [Ccolumn,ref,deficit,paid,Bcap,delta];ring

end SevenEighths.CenteredMomentEnergyCanonicalHighColumn

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalHighSource. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalHighSource

open OAI.SevenEighths.CenteredMomentEnergyCanonicalHighSource hiding actual_original_left_high_column

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power

open OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

open OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum

open OAI.SevenEighths.CenteredMomentFirstReferenceSource

open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily

open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility

open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows

open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice

open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower hiding actual_original_subsets_annular_power

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower

open OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLowColumn ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalHighColumn CenteredMomentFirstNonexceptionalLocalWeightSum

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn hiding actual_admitted_subsets_low_column

open OAI.SevenEighths.CenteredMomentEnergyCanonicalHighColumn hiding actual_admitted_subsets_high_column

theorem actual_original_left_high_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀_hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),τ=F.left ∨ τ=F.right →
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Mwidth≤Mdecl →
    Z^(Mwidth/4)≤src.X₁ → Z^(Mwidth/4)≤src.X₂ →
    Z^(Mwidth/4)≤src.Y₁ → Z^(Mwidth/4)≤src.Y₂ →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance C D Z);
    (commonEnergy (original src R0 seed0) C hC τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hlow⟩:=actual_admitted_subsets_high_column (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission N upper (max 1 b) (max 1 b) A 0 ξ
    hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_main_packet N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=OAI.SevenEighths.CenteredMomentEnergyFirstTwoSeedAdmission.eventually_error_packet
    N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ t
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZbaseLe
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints upper (max 1 b) (max 1 b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ a haPlain hW₁) (lower_profile_zero src.W₂ a haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedC:seed0∣C:=hcols.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hNC:(C.absNorm:ℝ)≤Z^(A+1):=hcols.2.2.2.2.2.1.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  have hTspan:=source_nominal_span src R0 seed0 K ⟨(C,D),hlabel⟩ E
  have hmod:τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}:=by
    rcases hτ with rfl|rfl
    · exact F.left_modulus
    · exact F.right_modulus
  obtain ⟨hPne,hPcard,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨υ,hυ,hbound⟩:=hfamilies τ
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E})
        K (volume src)) Z ξ:=by simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
    hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
    hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
    K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedC
    seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂
    hcap hMdecl hMwidth hdrop hclip hsourceLower
  intro B hB
  have hm:=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock false B t hB
  refine ⟨?_,?_⟩
  · have hmReady:Ready (child src C R0 B τ t) (R0*C)
        (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z (32*1) ξ) reserve)
        Z ξ (readyBudget A Pcap):=hm.1
    simpa only [mul_one] using hmReady
  · intro prime i χ Bp
    obtain ⟨_,_,_,hseparate,hpdata,_⟩:=hsep
    have hd:=elementPool_data _ (fun I hI=>(hpdata I hI).1)
      (fun I hI=>(hpdata I hI).2.1) prime.val prime.property
    let input:=child src C R0 B τ t
    let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun j=>w j.val
    have hsupp:∀j,Function.support (input.W j)⊆Set.Iic (max 1 bslot):=by
      intro j x hx
      exact ((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _)
    have hcop:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact CenteredMomentFirstAmplificationChoice.original_slot_coprime (original input (R0*C) seed).active
        Z sigma (max 1 bslot) eta hZ.le (by positivity) hseparate z (fun j=>hweta j.val)
        (fun j=>hmatch.scale j.val) hsupp (original input (R0*C) seed).active_slot
        (fun j I hI=>input.prime j I ((original input (R0*C) seed).active_subset _ hI))
        _ (hpdata _ hd.2.1).1 (hpdata _ hd.2.1).2.2.1
    have hk:errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by
      have hi:=errorIndex_cases i;omega
    have hrad:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have he:=herror.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock false B t seed hB M H fixedBadPrimes (Finset.Subset.refl _)
      prime.val prime.property (errorIndex i+1) hk hcop Bp χ
      (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
      (by simpa only [Nat.add_sub_cancel] using hrad)
    rcases he with hdead|hlive
    · exact Or.inl hdead.1
    · have hr:Ready (errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
          (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t)
          ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
          (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z (32*1) ξ) reserve prime.val (errorIndex i+1))
          Z ξ (readyBudget A Pcap):=hlive.1
      exact Or.inr (by simpa only [mul_one] using hr)

end SevenEighths.CenteredMomentEnergyCanonicalHighSource

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalRightSourceColumn. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn

open OAI.SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn hiding actual_original_right_high_column actual_original_right_low_column

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power

open OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

open OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum

open OAI.SevenEighths.CenteredMomentFirstReferenceSource

open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily

open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility

open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows

open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice

open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower hiding actual_original_subsets_annular_power

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower

open OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLowColumn OAI.SevenEighths.CenteredMomentFirstMixedRightTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn hiding actual_admitted_subsets_low_column

open OAI.SevenEighths.CenteredMomentFirstMixedRightTransport

open CenteredMomentFirstNonexceptionalLocalWeightSum

open OAI.SevenEighths.CenteredMomentEnergyFirstRightAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstRightAdmission

theorem actual_original_right_low_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),τ=F.right →
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Real.logb Z (volume src)≤5*Mdecl/6 →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(D.absNorm:ℝ))^2*Z^(OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance D C Z);
    (commonEnergy (original src R0 seed0) D hD τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hlow⟩:=actual_admitted_subsets_low_column (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission N upper (max 1 b) (max 1 b) A 0 ξ
    hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_right_main_packet N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=eventually_right_error_packet
    N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hlow t
  subst τ
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZbaseLe
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints upper (max 1 b) (max 1 b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ a haPlain hW₁) (lower_profile_zero src.W₂ a haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedD:seed0∣D:=hcols.2.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hND:(D.absNorm:ℝ)≤Z^(A+1):=hcols.2.2.2.2.2.2.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  have hTspan:=source_nominal_span src R0 seed0 K ⟨(C,D),hlabel⟩ E
  let Es:=swapSubset C D E
  have hmod:F.right.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es*activeConductor D C}:=by
    exact right_modulus src.η C D hC E χ₁ χ₂ F
  obtain ⟨hPne,hPcard,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨υ,hυ,hbound⟩:=hfamilies F.right
  have hnom:firstNominalScale D C
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es}) K (volume src)=
      firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src):=by
    dsimp only [Es]
    rw [swapSubset_generator,nominal_swap]
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale D C (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es})
        K (volume src)) Z ξ:=by
    rw [hnom]
    simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
    hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
    hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max D C R0 hD hC hCD.symm hR0 hRcap hND Es hmod
    K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedD
    seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hlow
    hcap hMdecl hMwidth hdrop hclip hsourceLower
  intro B hB
  have hm:=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock B t seed hB
  refine ⟨?_,?_⟩
  · simpa only [mul_one] using hm.2.1
  · intro prime i χ Bp
    obtain ⟨_,_,_,hseparate,hdata,_⟩:=hsep
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    let input:=child src D R0 B F.right t
    let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun j=>w j.val
    have hz:∀j,z j≤eta:=fun j=>hweta j.val
    have hlen:∀j,input.P j=Z^(z j):=fun j=>hmatch.scale j.val
    have hsupp:∀j,Function.support (input.W j)⊆Set.Iic (max 1 bslot):=by
      intro j x hx
      exact ((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _)
    have hslot:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact original_slot_coprime (original input (R0*D) seed).active Z sigma (max 1 bslot) eta
        hZ.le (by positivity) hseparate z hz hlen hsupp
        (original input (R0*D) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*D) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have he:=herror.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun j=>n j) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock B t seed hB M H fixedBadPrimes (Finset.Subset.refl _) prime.val prime.property
      (errorIndex i+1) hk' hslot Bp χ
      (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
      (by simpa only [Nat.add_sub_cancel] using hN)
    rcases he.2 with hdead|hlive
    · exact Or.inl hdead.1
    · exact Or.inr (by simpa only [mul_one] using hlive.1)

theorem actual_original_right_high_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),τ=F.right →
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Mwidth≤Mdecl →
    Z^(Mwidth/4)≤src.X₁ → Z^(Mwidth/4)≤src.X₂ →
    Z^(Mwidth/4)≤src.Y₁ → Z^(Mwidth/4)≤src.Y₂ →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(D.absNorm:ℝ))^2*Z^(OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance D C Z);
    (commonEnergy (original src R0 seed0) D hD τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hlow⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalHighColumn.actual_admitted_subsets_high_column (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission N upper (max 1 b) (max 1 b) A 0 ξ
    hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_right_main_packet N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=eventually_right_error_packet
    N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ t
  subst τ
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZbaseLe
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints upper (max 1 b) (max 1 b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ a haPlain hW₁) (lower_profile_zero src.W₂ a haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedD:seed0∣D:=hcols.2.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hND:(D.absNorm:ℝ)≤Z^(A+1):=hcols.2.2.2.2.2.2.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  have hTspan:=source_nominal_span src R0 seed0 K ⟨(C,D),hlabel⟩ E
  let Es:=swapSubset C D E
  have hmod:F.right.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es*activeConductor D C}:=by
    exact right_modulus src.η C D hC E χ₁ χ₂ F
  obtain ⟨hPne,hPcard,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨υ,hυ,hbound⟩:=hfamilies F.right
  have hnom:firstNominalScale D C
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es}) K (volume src)=
      firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (volume src):=by
    dsimp only [Es]
    rw [swapSubset_generator,nominal_swap]
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale D C (Ideal.span {primeSubsetGenerator (fun P:CommonIndex D C=>P.val) Es})
        K (volume src)) Z ξ:=by
    rw [hnom]
    simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
    hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
    hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max D C R0 hD hC hCD.symm hR0 hRcap hND Es hmod
    K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedD
    seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂
    hcap hMdecl hMwidth hdrop hclip hsourceLower
  intro B hB
  have hm:=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock B t seed hB
  refine ⟨?_,?_⟩
  · simpa only [mul_one] using hm.2.1
  · intro prime i χ Bp
    obtain ⟨_,_,_,hseparate,hdata,_⟩:=hsep
    have hd:=elementPool_data _ (fun Q hQ=>(hdata Q hQ).1)
      (fun Q hQ=>(hdata Q hQ).2.1) prime.val prime.property
    let input:=child src D R0 B F.right t
    let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun j=>w j.val
    have hz:∀j,z j≤eta:=fun j=>hweta j.val
    have hlen:∀j,input.P j=Z^(z j):=fun j=>hmatch.scale j.val
    have hsupp:∀j,Function.support (input.W j)⊆Set.Iic (max 1 bslot):=by
      intro j x hx
      exact ((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _)
    have hslot:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact original_slot_coprime (original input (R0*D) seed).active Z sigma (max 1 bslot) eta
        hZ.le (by positivity) hseparate z hz hlen hsupp
        (original input (R0*D) seed).active_slot
        (fun j Q hQ=>input.prime j Q ((original input (R0*D) seed).active_subset _ hQ))
        _ (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
    have hk:=errorIndex_cases i
    have hk':errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by omega
    have hN:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have he:=herror.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun j=>n j) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock B t seed hB M H fixedBadPrimes (Finset.Subset.refl _) prime.val prime.property
      (errorIndex i+1) hk' hslot Bp χ
      (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
      (by simpa only [Nat.add_sub_cancel] using hN)
    rcases he.2 with hdead|hlive
    · exact Or.inl hdead.1
    · exact Or.inr (by simpa only [mul_one] using hlive.1)

end SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalHighPhysical. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalHighPhysical

open OAI.SevenEighths.CenteredMomentEnergyCanonicalHighPhysical hiding actual_high_physical

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power

open OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

open OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum

open OAI.SevenEighths.CenteredMomentFirstReferenceSource

open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily

open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility

open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows

open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice

open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower hiding actual_original_subsets_annular_power

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower

open OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLowColumn CenteredMomentFirstNonexceptionalLocalWeightSum

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn hiding actual_admitted_subsets_low_column

theorem actual_high_physical
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(εphysical lowerProduct:ℝ)
    (hεphysical:0<εphysical)(hlowerProduct:0<lowerProduct):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cphysical:ℝ,0<Cphysical ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    lowerProduct≤(∏i,src.lo i)*a*a →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 → seed0≠0 →
    ∀K:ℝ,1≤K →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip ell:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Mwidth≤Mdecl →
    Z^(Mwidth/4)≤src.X₁ → Z^(Mwidth/4)≤src.X₂ →
    Z^(Mwidth/4)≤src.Y₁ → Z^(Mwidth/4)≤src.Y₂ →
    (∀j:Fin 4,
      OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma (frequencyLoss Z 32 ξ) reserve
        ((readyBudget A Pcap+readyBudget A Pcap)*εmask+εchild+εremove+
          (frequencyLoss Z 32 ξ+reserve+θsource)/6+θclip/3+κ*mesh)
        εsrc A saving j + εsrc*(A+1)+primeLoss ≤ ell) →
    CenteredMomentFirstSourceReduction.physicalMass src R0 seed0 fixedBadMask 1 (Ψ Aorig) K Z ξ /
      volume src ≤ Cphysical*(C₀+C₁+1)*(p.control Uprofile)^2*
        (1+|src.t|+height)^Jheight*Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
  obtain ⟨UL,JL,hleft⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalHighSource.actual_original_left_high_column
    (α:=α) M H hH Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask
    hMslot hεmask haPlain hbPlain L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  obtain ⟨UR,JR,hright⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn.actual_original_right_high_column
    (α:=α) M H hH Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask
    hMslot hεmask haPlain hbPlain L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  have hphysical (T:Finset α):=OAI.SevenEighths.CenteredMomentEnergyFirstPhysicalNormalization.actual_physical_mass_of_columnBounds
    (ι:=T) (Ψ T) JL JR (fun i=>|highs i.val|) (max 1 b) (max 1 b) A ξ εphysical
    lowerProduct hA hξ.le hεphysical hlowerProduct
  choose Cp hCp hp using hphysical
  let Cmass:ℝ:=1+∑T:Finset α,Cp T
  have hCmass:0<Cmass:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
    dsimp [Cmass];linarith
  have hCpCap (T:Finset α):Cp T≤Cmass:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
      (Finset.mem_univ T)
    dsimp [Cmass];linarith
  refine ⟨UL∪UR,2*(JL+JR),?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CL,hCL,ZL,hZL,hleft⟩:=hleft η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CR,hCR,ZR,hZR,hright⟩:=hright η₀ Q hQM hQ0 hQt hQ72
  have hmL:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JL
  have hmR:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JR
  let Cm:ℝ:=Cmass*(CL+CR)*(1+CenteredMomentSecondWindowBudget.profileMoment JL)*
    (1+CenteredMomentSecondWindowBudget.profileMoment JR)
  have hCm:0<Cm:=by dsimp [Cm];positivity
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hp
  obtain ⟨Zp,hZp⟩:=Filter.eventually_atTop.mp hall
  refine ⟨Cm,hCm,max Zp (max ZL ZR),lt_of_lt_of_le hZL
    ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max hprod R0 seed0 hR0 hRcap hseed0 hseed00 K hK1 p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip ell hθclip hMA hcap hMdecl hMwidth hdrop
    hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ hfit
  have hZL':ZL≤Z:=(le_max_left _ _).trans ((le_max_right _ _).trans hZZ)
  have hZR':ZR≤Z:=(le_max_right _ _).trans ((le_max_right _ _).trans hZZ)
  have hZ:1<Z:=hZL.trans_le hZL'
  have hz:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs (by
    have hh:=hcap.trans hMA
    simpa only [hmatch.scale,Real.logb_rpow hz hZ.ne'] using hh)
  have hKi:K⁻¹≤Z^A:=(inv_le_one_of_one_le₀ hK1).trans (Real.one_le_rpow hZ.le hA)
  have hs₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx;rw [←hp₁] at hx;exact (p.support 0 hx).1
  have hs₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx;rw [←hp₂] at hx;exact (p.support 1 hx).1
  let delta:=frequencyLoss Z 32 ξ
  let paid:=(readyBudget A Pcap+readyBudget A Pcap)*εmask+εchild+εremove+
    (delta+reserve+θsource)/6+θclip/3+κ*mesh
  let powers:Fin 4→ℝ:=fun j=>
    OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma delta reserve paid εsrc A saving j
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let base:=εsrc*(A+1)+primeLoss
  let FL:=CL*(C₀+C₁+1)*(p.control UL)^2*(1+height)^JL
  let FR:=CR*(C₀+C₁+1)*(p.control UR)^2*(1+height)^JR
  let Fcap:ℝ:=(CL+CR)*(C₀+C₁+1)*(p.control (UL∪UR))^2*(1+height)^(JL+JR)
  let frontL:=FL*Z^(deficit+base)
  let frontR:=FR*Z^(deficit+base)
  have hfrontL:0≤frontL:=by dsimp [frontL,FL];positivity
  have hfrontR:0≤frontR:=by dsimp [frontR,FR];positivity
  have hFcap:0≤Fcap:=by dsimp [Fcap];positivity
  have hcontrol (S₁:Finset (ℕ×ℕ))(hs:S₁⊆UL∪UR):p.control S₁≤p.control (UL∪UR):=by
    unfold Profiles.control
    exact mul_le_mul
      (Seminorm.le_def.mp (Finset.sup_mono hs) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hs) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hFL:FL≤Fcap:=by
    dsimp [FL,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UL
    · exact hcontrol UL Finset.subset_union_left
    · linarith
    · omega
  have hFR:FR≤Fcap:=by
    dsimp [FR,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UR
    · exact hcontrol UR Finset.subset_union_right
    · linarith
    · omega
  have hcoeff (F:ℝ)(hF:F≤Fcap)(j:Fin 4):
      (F*Z^(deficit+base))*Z^(powers j)≤Fcap*Z^(deficit+ell):=by
    rw [mul_assoc,←Real.rpow_add hz]
    apply mul_le_mul hF (Real.rpow_le_rpow_of_exponent_le hZ.le ?_) (Real.rpow_nonneg hz.le _) hFcap
    have hh:powers j+base≤ell:=by
      dsimp [powers,base,paid,delta]
      linarith [hfit j]
    linarith
  have hcols (lab:CenteredMomentFirstNonexceptionalWeightSum.Labels src R0 seed0)
      (E:Finset (CommonIndex lab.val.1 lab.val.2))
      (n:OAI.SevenEighths.CenteredMomentFirstReferenceSource.SourceBlocks src R0 seed0 K Z ξ lab E)
      (hne:originalBlock src R0 seed0 (Ψ T) K Z ξ lab E n≠0):
      OAI.SevenEighths.CenteredMomentFirstReferenceEnergy.ColumnBounds src R0 seed0 Z JL JR
        (fun j=>frontL*Z^(powers j)) (fun j=>frontR*Z^(powers j)) lab E (fun i=>(n i).val):=by
    apply OAI.SevenEighths.CenteredMomentEnergyFirstColumnPairing.column_bounds_of_reference_sums
    · intro innerL hLcap hLsq χ v
      let hs:=OAI.SevenEighths.CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hleft T θ Z hZL' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.left (Or.inl rfl)
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ v
      simpa only [frontL,FL,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
    · intro innerL hLcap hLsq χ v
      let hs:=OAI.SevenEighths.CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hright T θ Z hZR' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.right rfl
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hwidthle hrawX₁ hrawX₂ hrawY₁ hrawY₂ v
      simpa only [frontR,FR,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
  have hmass:=(hZp Z ((le_max_left _ _).trans hZZ) T) src R0 seed0 hseed0 hseed00
    (fun i=>by rw [hhiSrc]) (by rwa [abs_of_nonneg hb1]) (by rwa [abs_of_nonneg hb2])
    a a K haPlain haPlain hK hprod hs₁ hs₂ hV hKi Fcap Mdecl ell (fun _=>ell) (fun _=>ell)
    (fun j=>frontL*Z^(powers j)) (fun j=>frontR*Z^(powers j)) hFcap
    (fun j=>mul_nonneg hfrontL (Real.rpow_nonneg hz.le _))
    (fun j=>mul_nonneg hfrontR (Real.rpow_nonneg hz.le _))
    (hcoeff FL hFL) (hcoeff FR hFR) (fun _=>le_rfl)
    (fun _=>le_rfl) (fun lab E _ n hne=>hcols lab E n hne)
  have hconst:Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
      CenteredMomentSecondWindowBudget.profileMoment JR≤Cm:=by
    dsimp [Cm]
    gcongr
    · exact hCpCap T
    · linarith
    · linarith
  have hheightProduct:(1+height)^(JL+JR)*(1+|src.t|)^(JL+JR)≤
      (1+|src.t|+height)^(2*(JL+JR)):=by
    have heq:(1+|src.t|+height)^(2*(JL+JR))=
        (1+|src.t|+height)^(JL+JR)*(1+|src.t|+height)^(JL+JR):=by
      rw [show 2*(JL+JR)=(JL+JR)+(JL+JR) by omega]
      exact pow_add _ _ _
    rw [heq]
    apply mul_le_mul
      (pow_le_pow_left₀ (by linarith) (by linarith [abs_nonneg src.t]) _)
      (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (by positivity) (by positivity)
  calc
    _ ≤ (Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
          CenteredMomentSecondWindowBudget.profileMoment JR)*(C₀+C₁+1)*
          (p.control (UL∪UR))^2*((1+height)^(JL+JR)*(1+|src.t|)^(JL+JR))*
          Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
      apply hmass.trans_eq
      dsimp [Fcap]
      ring
    _ ≤ _ := by gcongr

end SevenEighths.CenteredMomentEnergyCanonicalHighPhysical

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalLowSource. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLowSource

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLowSource hiding actual_original_left_low_column

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power

open OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

open OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum

open OAI.SevenEighths.CenteredMomentFirstReferenceSource

open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily

open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility

open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows

open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice

open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower hiding actual_original_subsets_annular_power

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower

open OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLowColumn CenteredMomentFirstNonexceptionalLocalWeightSum

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn hiding actual_admitted_subsets_low_column

theorem actual_original_left_low_column
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Ccolumn:ℝ,0<Ccolumn ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 →
    ∀(C D:Ideal O),∀hC:Supported C,∀_hD:Supported D,
    ∀hlabel:(C,D)∈CenteredMomentFirstSectors.commonLabels
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0)))
      (CenteredMomentSourceRow.supportedColumns (activeSource
        (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R0 seed0))),
    ∀(E:Finset (CommonIndex C D))(χ₁ χ₂:RayCharacter),
    ∀F:FixedPair src.η C D hC E χ₁ χ₂,
    ∀(τ:Character),τ=F.left ∨ τ=F.right →
    ∀K:ℝ,1≤K →
    ∀Wphysical:𝓢(ℝ,ℂ),∀n:SourceBlocks src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E,
    originalBlock src R0 seed0 Wphysical K Z ξ ⟨(C,D),hlabel⟩ E n≠0 →
    ∀(seed:Ideal O),Squarefree seed → (seed.absNorm:ℝ)≤sourceRadius src/(D.absNorm:ℝ) →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Real.logb Z (volume src)≤5*Mdecl/6 →
    ∀t:ℝ,
    let delta:=frequencyLoss Z 32 ξ;
    let Bcap:=readyBudget A Pcap;
    let paid:=(Bcap+Bcap)*εmask+εchild+εremove+(delta+reserve+θsource)/6+θclip/3+κ*mesh;
    let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ));
    let ref:=(τ.modulus.absNorm:ℝ)*(volume src/(C.absNorm:ℝ))^2*Z^(OAI.SevenEighths.CenteredMomentFirstMixedAllowance.allowance C D Z);
    (commonEnergy (original src R0 seed0) C hC τ t seed
      CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re≤
      (ref/(seed.absNorm:ℝ))*(Ccolumn*(C₀+C₁+1)*(p.control Uprofile)^2*(1+height)^Jheight*
        Z^(deficit+εsrc*(A+1)+primeLoss)*
        ∑j:Fin 4,Z^(OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc Bcap j+
          lossVector sigma delta reserve paid εsrc A saving j))*(1+|t|)^(2*Jheight) :=by
  obtain ⟨U,J,hlow⟩:=actual_admitted_subsets_low_column (α:=α) M H hH
    Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain hbPlain
    L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ N lower upper a0 θsource
    hlower hupper ha0 hθsource lows highs hhighs εsrc δsrc θsrc Bseed ξ saving
    hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall A Pcap eta primeLoss reserve
    hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Ccolumn,hCcolumn,Zbase,hZbase,hcolumn⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
  have hsourceEvent:=eventually_source_admission N upper (max 1 b) (max 1 b) A 0 ξ
    hupper (by positivity) (by positivity)
  have hmainEvent:=eventually_main_packet N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  have hsepEvent:=CenteredMomentFirstAmplificationChoice.eventually_dyadic_amplification.{0}
    M H hH fixedBadPrimes (Finset.Subset.refl _) sigma primeLoss (Pcap+A+1) Bseed
      (amplifierCap A 0 ξ) (max 1 bslot) eta hsigma hPrimeLoss
      (by unfold amplifierCap;positivity) heta
  have herrorEvent:=OAI.SevenEighths.CenteredMomentEnergyFirstTwoSeedAdmission.eventually_error_packet
    N upper (max 1 b) (max 1 b) lower a A Pcap
    hupper (le_max_left _ _) (le_max_left _ _) hlower haPlain hA hPcap
  obtain ⟨Zth,hZth⟩:=Filter.eventually_atTop.mp
    (hsourceEvent.and (hmainEvent.and (herrorEvent.and (hsepEvent.and (eventually_ge_atTop Zbase)))))
  refine ⟨Ccolumn,hCcolumn,max Zth Zbase,lt_of_lt_of_le hZbase (le_max_right _ _),?_⟩
  intro Aorig θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K hK1 Wphysical n hblock seed hseed hseedcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
    Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hlow t
  obtain ⟨hsource,hmain,herror,hsep,hZbaseLe⟩:=hZth Z ((le_max_left _ _).trans hZZ)
  have hZ:1<Z:=hZbase.trans_le hZbaseLe
  have hZpos:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hlogs:∀i,Real.logb Z (src.P i)=w i:=by
    intro i;rw [hmatch.scale,Real.logb_rpow hZpos hZ.ne']
  have hcapacity:length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤A:=by
    simpa only [hlogs] using hcap.trans hMA
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs hcapacity
  have hηcap:(src.η.modulus.absNorm:ℝ)≤Z^A:=by
    have hlogK:=Real.logb_nonneg hZ hK1
    have hηpos:=CenteredMomentFirstScale.norm_pos _ src.η.modulus_ne_bot
    apply (Real.logb_le_iff_le_rpow hZ hηpos).mp
    linarith only [hMdecl,hMA,hlogK]
  have hMdecl0:0≤Mdecl:=by
    have hk:=Real.logb_nonneg hZ hK1
    have hn:1≤(src.η.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr src.η.modulus_ne_bot)
    have hη:=Real.logb_nonneg hZ hn
    linarith only [hMdecl,hk,hη]
  have hends:Endpoints upper (max 1 b) (max 1 b) src:=
    ⟨hupperSrc,(fun i=>by rw [hhiSrc i];exact hhighs i.val),hb1,hb1max,hb2,hb2max⟩
  have hW₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 0 x≠0:=by simpa only [hp₁] using hx
    exact (p.support 0 hh).1
  have hW₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx
    have hh:p.profile 1 x≠0:=by simpa only [hp₂] using hx
    exact (p.support 1 hh).1
  have hcols:=actual_common_gates src R0 seed0 hseed0
    (lower_profile_zero src.W₁ a haPlain hW₁) (lower_profile_zero src.W₂ a haPlain hW₂) C D hlabel
  have hCD:primeSupport C=primeSupport D:=hcols.2.2.1
  have hseedC:seed0∣C:=hcols.2.2.2.1
  have hDnorm:1≤(D.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hradius:=hsource.2 Aorig src hcard
    (fun i=>by rw [abs_of_nonneg (hends.2.1 i)];exact (src.upper_ge i).trans hupperSrc)
    (by simpa only [abs_of_nonneg hb1] using hb1max)
    (by simpa only [abs_of_nonneg hb2] using hb2max) R0 seed0 K ξ hK le_rfl hV
    (by simpa only [Real.rpow_zero] using inv_le_one_of_one_le₀ hK1)
  have hNC:(C.absNorm:ℝ)≤Z^(A+1):=hcols.2.2.2.2.2.1.trans hradius.1
  have hseedne:seed≠0:=hseed.ne_zero
  have hseedCap:(seed.absNorm:ℝ)≤Z^Bseed:=by
    calc
      _≤sourceRadius src/(D.absNorm:ℝ):=hseedcap
      _≤sourceRadius src:=div_le_self ((Nat.cast_nonneg C.absNorm).trans hcols.2.2.2.2.2.1) hDnorm
      _≤Z^(A+1):=hradius.1
      _≤Z^Bseed:=Real.rpow_le_rpow_of_exponent_le hZ.le hBseed
  have hamp:=(hradius.2 ⟨(C,D),hlabel⟩ E n)
  have hTspan:=source_nominal_span src R0 seed0 K ⟨(C,D),hlabel⟩ E
  have hmod:τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}:=by
    rcases hτ with rfl|rfl
    · exact F.left_modulus
    · exact F.right_modulus
  obtain ⟨hPne,hPcard,hfamilies⟩:=hcolumn Z hZbaseLe
  obtain ⟨υ,hυ,hbound⟩:=hfamilies τ
  have houter:dyadicScale (n 1)≤4*frequencyRadius
      (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E})
        K (volume src)) Z ξ:=by simpa only [primeSubsetGenerator,span_idealGenerator,CenteredMomentExceptionalAmplitudePair.volume,CenteredMomentAmplificationChildInput.volume] using hamp.2.2.1
  apply hbound Aorig θ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
    hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
    hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max C D R0 hC hD hCD hR0 hRcap hNC E hmod
    K (dyadicScale (n 1)) hK (zero_lt_one.trans hamp.2.1) houter hamp.2.2.2.1 t seed0 hseedC
    seed hseed hseedne hseedCap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip hθclip hMdecl0 hMA hlow
    hcap hMdecl hMwidth hdrop hclip hsourceLower
  intro B hB
  have hm:=hmain.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
    R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
    K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
    hK (by norm_num) hsigma.le hξ.le hξ1 hreserve.le hamp.2.2.2.2
    (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
    Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
    hblock false B t hB
  refine ⟨?_,?_⟩
  · have hmReady:Ready (child src C R0 B τ t) (R0*C)
        (mainRadius C D E K (volume src) Z sigma (frequencyLoss Z (32*1) ξ) reserve)
        Z ξ (readyBudget A Pcap):=hm.1
    simpa only [mul_one] using hmReady
  · intro prime i χ Bp
    obtain ⟨_,_,_,hseparate,hpdata,_⟩:=hsep
    have hd:=elementPool_data _ (fun I hI=>(hpdata I hI).1)
      (fun I hI=>(hpdata I hI).2.1) prime.val prime.property
    let input:=child src C R0 B τ t
    let z:CenteredMomentCommonProfile.liveIndices B.val→ℝ:=fun j=>w j.val
    have hsupp:∀j,Function.support (input.W j)⊆Set.Iic (max 1 bslot):=by
      intro j x hx
      exact ((src.support j.val hx).2.trans (hhi j.val)).trans (le_max_right _ _)
    have hcop:∀j,∀I∈(activeInput input).slots j,IsCoprime (Ideal.span {prime.val}) I:=by
      exact CenteredMomentFirstAmplificationChoice.original_slot_coprime (original input (R0*C) seed).active
        Z sigma (max 1 bslot) eta hZ.le (by positivity) hseparate z (fun j=>hweta j.val)
        (fun j=>hmatch.scale j.val) hsupp (original input (R0*C) seed).active_slot
        (fun j I hI=>input.prime j I ((original input (R0*C) seed).active_subset _ hI))
        _ (hpdata _ hd.2.1).1 (hpdata _ hd.2.1).2.2.1
    have hk:errorIndex i+1=1∨errorIndex i+1=6∨errorIndex i+1=7:=by
      have hi:=errorIndex_cases i;omega
    have hrad:=hυ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ
    have he:=herror.2 src hcard hends hlowerSrc hW₁ hW₂ κ hκsmall hPs hcapacity hηcap
      R0 seed0 hR0 hRcap hseed0 C D hC hD hlabel E χ₁ χ₂ F τ hτ
      K 1 (firstNominalScale C D (∏P∈E,P.val) K (volume src)) sigma ξ reserve
      hK (by norm_num) hsigma.le hsigma1 hξ.le hξ1 hreserve.le hamp.2.2.2.2
      (retainedRows (localRadius src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E) 1)
      Wphysical (fun i=>n i) (source_dyad_retained src R0 seed0 K Z ξ ⟨(C,D),hlabel⟩ E n)
      hblock false B t seed hB M H fixedBadPrimes (Finset.Subset.refl _)
      prime.val prime.property (errorIndex i+1) hk hcop Bp χ
      (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t
      (by simpa only [Nat.add_sub_cancel] using hrad)
    rcases he with hdead|hlive
    · exact Or.inl hdead.1
    · have hr:Ready (errorInput src C R0 B τ t (Ideal.span {prime.val}) (errorIndex i+1) Bp
          (υ Aorig (CenteredMomentCommonProfile.liveIndices B.val) prime i χ) t)
          ((R0*C)*(Ideal.span {prime.val})^(errorIndex i+1))
          (errorRadius C D E K (volume src) Z sigma (frequencyLoss Z (32*1) ξ) reserve prime.val (errorIndex i+1))
          Z ξ (readyBudget A Pcap):=hlive.1
      exact Or.inr (by simpa only [mul_one] using hr)

end SevenEighths.CenteredMomentEnergyCanonicalLowSource

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CanonicalLowPhysical. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCanonicalLowPhysical

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLowPhysical hiding actual_low_physical

open HeckeFamily ConcreteTraceCRT

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile

open CenteredMomentRadialEligibleEnergy

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLiveBound OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveBound hiding actual_live_canonical_child_bands

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLiveCapacity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalPaidSource ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid

open OAI.SevenEighths.CenteredMomentEnergyCanonicalPaidSource hiding actual_canonical_paid_source

open OAI.SevenEighths.CenteredMomentEnergyCanonicalCommonPaid hiding actual_common_paid_source

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentEnergyCanonicalReferencePaid hiding actual_reference_paid_source

open OAI.SevenEighths.CenteredMomentEnergyBandSubtypeTransport

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedClipped ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous

open OAI.SevenEighths.CenteredMomentEnergyAllocatedClipped hiding actual_clipped_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedHomogeneous hiding actual_clipped_homogeneous_bands

open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles

open OAI.SevenEighths.CenteredMomentEnergyAllocatedPaid hiding actual_allocated_paid_bands

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren

open OAI.SevenEighths.CenteredMomentEnergyAllocatedZero

open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw

open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open OAI.SevenEighths.CenteredMomentAllocatedRayDictionary

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization

open OAI.SevenEighths.CenteredMomentEnergyCanonicalChildBound hiding actual_canonical_child_bands

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalUniformReference OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentEnergyCanonicalUniformReference hiding original_subsets_reference_paid

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedRayDictionary

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open OAI.SevenEighths.CenteredMomentFirstAmplifiedPaidAdmission

open OAI.SevenEighths.CenteredMomentFirstAmplifiedCapacityCommon

open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss

open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic

open CenteredMomentSecondHeightFamily

open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open RayFourExpansion CenteredMomentSourceMass CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondEnergySplit CenteredMomentGaussNormalization

open Filter CenteredMomentOriginalCommonHarmonic CenteredMomentActiveSource

open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate CenteredMomentSecondWindowSource

open CenteredMomentFirstChildProfileControl CenteredMomentSecondChildPowerBudget

open CenteredMomentSecondSourceSeededPowerDescent CenteredMomentSecondReferenceNormalization

open CenteredMomentFirstSeededGaussianPower CenteredMomentFirstSecondInputGates

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput

open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open OAI.SevenEighths.CenteredMomentEnergyAmplifiedChildWidth

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedUniform hiding actual_original_subsets_amplified_power

open OAI.SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstAnnularAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

open OAI.SevenEighths.CenteredMomentEnergyInputParentCapacity

open OAI.SevenEighths.CenteredMomentFirstReferenceSource CenteredMomentFirstNonexceptionalWeightSum

open OAI.SevenEighths.CenteredMomentFirstReferenceSource

open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationRadicalFamily

open CenteredMomentAmplificationActiveFactor CenteredMomentAmplificationEligibility

open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows

open CenteredMomentFirstAmplifiedPowerBudget CenteredMomentFirstAmplificationChoice

open CenteredMomentSecondRetainedRows CenteredMomentLogDyadic

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAnnularPower hiding actual_original_subsets_annular_power

open OAI.SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open OAI.SevenEighths.CenteredMomentFirstCommonReferencePower

open OAI.SevenEighths.CenteredMomentEnergyFirstLowHomogeneousPowers

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLowColumn CenteredMomentFirstNonexceptionalLocalWeightSum

open OAI.SevenEighths.CenteredMomentEnergyCanonicalLowColumn hiding actual_admitted_subsets_low_column

theorem actual_low_physical
    (Wslot:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤Mslot)(hεmask:0<εmask)(haPlain:0<a)(hbPlain:0≤b)
    (L:ℝ)(hL:0≤L)(degree:ℕ)(S:Finset (ℕ×ℕ))
    (ha:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hMcap:0≤Mcap)(hLs:0≤Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)
    (hκ:1 ≤ κ)
    (N:ℕ)(lower upper a0 θsource:ℝ)(hlower:0<lower)(hupper:1≤upper)
    (ha0:0<a0)(hθsource:0<θsource)
    (lows highs:α→ℝ)(hhighs:∀i,0≤highs i)
    (εsrc δsrc θsrc Bseed ξ saving:ℝ)
    (hεsrc:0<εsrc)(hδsrc:0<δsrc)(hθsrc:0<θsrc)(hξ:0<ξ)
    (sigma:ℝ)(hsigma:0<sigma)(hξsmall:ξ≤sigma/4)(A Pcap eta primeLoss reserve:ℝ)
    (hA:0≤A)(hPcap:0≤Pcap)(heta:eta<sigma/6)(hPrimeLoss:0<primeLoss)
    (hsigma1:sigma≤1)(hξ1:ξ≤1)(hreserve:0<reserve)
    (heps1:εsrc≤1)(hBseed:A+1≤Bseed)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(εphysical lowerProduct:ℝ)
    (hεphysical:0<εphysical)(hlowerProduct:0<lowerProduct):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M →
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cphysical:ℝ,0<Cphysical ∧ ∃Z₀:ℝ,1<Z₀ ∧
    ∀Aorig:Finset α,∀θ:Aorig→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤Z →
    ∀εchild:ℝ,∀C₀ C₁:ℝ,0≤C₀ → 0≤C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:Aorig→ℝ)(height mesh:ℝ),0≤mesh → (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤eta) →
    (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤height → (∀i,|freq i|≤height) →
    ∀src:Input Aorig,Matches M H hH src η₀ θ w σ freq Wslot bslot Z →
    (∀i,src.hi i≤bslot) → (∀i,src.M i≤Mslot) →
    (∀i,src.lo i=lows i.val) → (∀i,src.hi i=highs i.val) →
    Fintype.card Aorig≤N → lower≤src.lower → src.upper≤upper →
    0≤src.b₁ → 0≤src.b₂ → src.b₁≤max 1 b → src.b₂≤max 1 b →
    lowerProduct≤(∏i,src.lo i)*a*a →
    ∀(R0 seed0:Ideal O),R0≠0 → (R0.absNorm:ℝ)≤Z^Pcap → Squarefree seed0 → seed0≠0 →
    ∀K:ℝ,1≤K →
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤Z^L → src.X₂≤Z^L → src.Y₁≤Z^L → src.Y₂≤Z^L →
    ∀Mdecl Mwidth θclip ell:ℝ,0≤θclip → Mdecl≤A →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤Mwidth →
    Mwidth-sigma/2≤Mcap →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    a0≤OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N lower a →
    Real.logb Z (volume src)≤5*Mdecl/6 →
    (∀j:Fin 4,
      OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma (frequencyLoss Z 32 ξ) reserve
        ((readyBudget A Pcap+readyBudget A Pcap)*εmask+εchild+εremove+
          (frequencyLoss Z 32 ξ+reserve+θsource)/6+θclip/3+κ*mesh)
        εsrc A saving j + εsrc*(A+1)+primeLoss ≤ ell) →
    CenteredMomentFirstSourceReduction.physicalMass src R0 seed0 fixedBadMask 1 (Ψ Aorig) K Z ξ /
      volume src ≤ Cphysical*(C₀+C₁+1)*(p.control Uprofile)^2*
        (1+|src.t|+height)^Jheight*Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
  obtain ⟨UL,JL,hleft⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLowSource.actual_original_left_low_column
    (α:=α) M H hH Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask
    hMslot hεmask haPlain hbPlain L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  obtain ⟨UR,JR,hright⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalRightSourceColumn.actual_original_right_low_column
    (α:=α) M H hH Wslot aslot bslot Mcap Lslot εremove lo hi κ a b Mslot εmask
    hMslot hεmask haPlain hbPlain L hL degree S ha hWs hW hMcap hLs hε hκsmall  hκ
    N lower upper a0 θsource hlower hupper ha0 hθsource lows highs hhighs
    εsrc δsrc θsrc Bseed ξ saving hεsrc hδsrc hθsrc hξ sigma hsigma hξsmall
    A Pcap eta primeLoss reserve hA hPcap heta hPrimeLoss hsigma1 hξ1 hreserve heps1 hBseed
  have hphysical (T:Finset α):=OAI.SevenEighths.CenteredMomentEnergyFirstPhysicalNormalization.actual_physical_mass_of_columnBounds
    (ι:=T) (Ψ T) JL JR (fun i=>|highs i.val|) (max 1 b) (max 1 b) A ξ εphysical
    lowerProduct hA hξ.le hεphysical hlowerProduct
  choose Cp hCp hp using hphysical
  let Cmass:ℝ:=1+∑T:Finset α,Cp T
  have hCmass:0<Cmass:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
    dsimp [Cmass];linarith
  have hCpCap (T:Finset α):Cp T≤Cmass:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCp T).le)
      (Finset.mem_univ T)
    dsimp [Cmass];linarith
  refine ⟨UL∪UR,2*(JL+JR),?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CL,hCL,ZL,hZL,hleft⟩:=hleft η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨CR,hCR,ZR,hZR,hright⟩:=hright η₀ Q hQM hQ0 hQt hQ72
  have hmL:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JL
  have hmR:=CenteredMomentSecondWindowBudget.profileMoment_nonneg JR
  let Cm:ℝ:=Cmass*(CL+CR)*(1+CenteredMomentSecondWindowBudget.profileMoment JL)*
    (1+CenteredMomentSecondWindowBudget.profileMoment JR)
  have hCm:0<Cm:=by dsimp [Cm];positivity
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hp
  obtain ⟨Zp,hZp⟩:=Filter.eventually_atTop.mp hall
  refine ⟨Cm,hCm,max Zp (max ZL ZR),lt_of_lt_of_le hZL
    ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh hmesh hw hwm hweta hwL
    hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc hcard hlowerSrc hupperSrc
    hb1 hb2 hb1max hb2max hprod R0 seed0 hR0 hRcap hseed0 hseed00 K hK1 p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl Mwidth θclip ell hθclip hMA hcap hMdecl hMwidth hdrop
    hclip hsourceLower hlow hfit
  have hZL':ZL≤Z:=(le_max_left _ _).trans ((le_max_right _ _).trans hZZ)
  have hZR':ZR≤Z:=(le_max_right _ _).trans ((le_max_right _ _).trans hZZ)
  have hZ:1<Z:=hZL.trans_le hZL'
  have hz:0<Z:=zero_lt_one.trans hZ
  have hK:0<K:=zero_lt_one.trans_le hK1
  have hPs:∀i,1≤src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hZ.le (hw i)
  have hV:volume src≤Z^A:=original_volume_cap src Z κ A hZ hκsmall hPs (by
    have hh:=hcap.trans hMA
    simpa only [hmatch.scale,Real.logb_rpow hz hZ.ne'] using hh)
  have hKi:K⁻¹≤Z^A:=(inv_le_one_of_one_le₀ hK1).trans (Real.one_le_rpow hZ.le hA)
  have hs₁:∀x,src.W₁ x≠0→a≤x:=by
    intro x hx;rw [←hp₁] at hx;exact (p.support 0 hx).1
  have hs₂:∀x,src.W₂ x≠0→a≤x:=by
    intro x hx;rw [←hp₂] at hx;exact (p.support 1 hx).1
  let delta:=frequencyLoss Z 32 ξ
  let paid:=(readyBudget A Pcap+readyBudget A Pcap)*εmask+εchild+εremove+
    (delta+reserve+θsource)/6+θclip/3+κ*mesh
  let powers:Fin 4→ℝ:=fun j=>
    OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights.losses εsrc δsrc θsrc (readyBudget A Pcap) j+
      lossVector sigma delta reserve paid εsrc A saving j
  let deficit:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))
  let base:=εsrc*(A+1)+primeLoss
  let FL:=CL*(C₀+C₁+1)*(p.control UL)^2*(1+height)^JL
  let FR:=CR*(C₀+C₁+1)*(p.control UR)^2*(1+height)^JR
  let Fcap:ℝ:=(CL+CR)*(C₀+C₁+1)*(p.control (UL∪UR))^2*(1+height)^(JL+JR)
  let frontL:=FL*Z^(deficit+base)
  let frontR:=FR*Z^(deficit+base)
  have hfrontL:0≤frontL:=by dsimp [frontL,FL];positivity
  have hfrontR:0≤frontR:=by dsimp [frontR,FR];positivity
  have hFcap:0≤Fcap:=by dsimp [Fcap];positivity
  have hcontrol (S₁:Finset (ℕ×ℕ))(hs:S₁⊆UL∪UR):p.control S₁≤p.control (UL∪UR):=by
    unfold Profiles.control
    exact mul_le_mul
      (Seminorm.le_def.mp (Finset.sup_mono hs) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hs) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hFL:FL≤Fcap:=by
    dsimp [FL,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UL
    · exact hcontrol UL Finset.subset_union_left
    · linarith
    · omega
  have hFR:FR≤Fcap:=by
    dsimp [FR,Fcap]
    gcongr
    · linarith
    · exact p.control_nonneg UR
    · exact hcontrol UR Finset.subset_union_right
    · linarith
    · omega
  have hcoeff (F:ℝ)(hF:F≤Fcap)(j:Fin 4):
      (F*Z^(deficit+base))*Z^(powers j)≤Fcap*Z^(deficit+ell):=by
    rw [mul_assoc,←Real.rpow_add hz]
    apply mul_le_mul hF (Real.rpow_le_rpow_of_exponent_le hZ.le ?_) (Real.rpow_nonneg hz.le _) hFcap
    have hh:powers j+base≤ell:=by
      dsimp [powers,base,paid,delta]
      linarith [hfit j]
    linarith
  have hcols (lab:CenteredMomentFirstNonexceptionalWeightSum.Labels src R0 seed0)
      (E:Finset (CommonIndex lab.val.1 lab.val.2))
      (n:OAI.SevenEighths.CenteredMomentFirstReferenceSource.SourceBlocks src R0 seed0 K Z ξ lab E)
      (hne:originalBlock src R0 seed0 (Ψ T) K Z ξ lab E n≠0):
      OAI.SevenEighths.CenteredMomentFirstReferenceEnergy.ColumnBounds src R0 seed0 Z JL JR
        (fun j=>frontL*Z^(powers j)) (fun j=>frontR*Z^(powers j)) lab E (fun i=>(n i).val):=by
    apply OAI.SevenEighths.CenteredMomentEnergyFirstColumnPairing.column_bounds_of_reference_sums
    · intro innerL hLcap hLsq χ v
      let hs:=OAI.SevenEighths.CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hleft T θ Z hZL' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.left (Or.inl rfl)
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hlow v
      simpa only [frontL,FL,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
    · intro innerL hLcap hLsq χ v
      let hs:=OAI.SevenEighths.CenteredMomentFirstReferenceEnergy.supported src R0 seed0 lab
      let family:=fixedPair src.η lab.val.1 lab.val.2 hs.1 E χ χ
      have hh:=hright T θ Z hZR' εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height mesh
        hmesh hw hwm hweta hwL hσlo hσhi hheight hfreq src hmatch hhi hMs hloSrc hhiSrc
        hcard hlowerSrc hupperSrc hb1 hb2 hb1max hb2max R0 seed0 hR0 hRcap hseed0
        lab.val.1 lab.val.2 hs.1 hs.2 lab.property E χ χ family family.right rfl
        K hK1 (Ψ T) n hne innerL hLsq hLcap p hp₁ hp₂ hX₁ hX₂ hY₁ hY₂
        Mdecl Mwidth θclip hθclip hMA hcap hMdecl hMwidth hdrop hclip hsourceLower hlow v
      simpa only [frontR,FR,powers,delta,paid,deficit,base,add_assoc,family,hs,
        CenteredMomentAmplificationChildInput.volume,CenteredMomentExceptionalAmplitudePair.volume] using hh
  have hmass:=(hZp Z ((le_max_left _ _).trans hZZ) T) src R0 seed0 hseed0 hseed00
    (fun i=>by rw [hhiSrc]) (by rwa [abs_of_nonneg hb1]) (by rwa [abs_of_nonneg hb2])
    a a K haPlain haPlain hK hprod hs₁ hs₂ hV hKi Fcap Mdecl ell (fun _=>ell) (fun _=>ell)
    (fun j=>frontL*Z^(powers j)) (fun j=>frontR*Z^(powers j)) hFcap
    (fun j=>mul_nonneg hfrontL (Real.rpow_nonneg hz.le _))
    (fun j=>mul_nonneg hfrontR (Real.rpow_nonneg hz.le _))
    (hcoeff FL hFL) (hcoeff FR hFR) (fun _=>le_rfl)
    (fun _=>le_rfl) (fun lab E _ n hne=>hcols lab E n hne)
  have hconst:Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
      CenteredMomentSecondWindowBudget.profileMoment JR≤Cm:=by
    dsimp [Cm]
    gcongr
    · exact hCpCap T
    · linarith
    · linarith
  have hheightProduct:(1+height)^(JL+JR)*(1+|src.t|)^(JL+JR)≤
      (1+|src.t|+height)^(2*(JL+JR)):=by
    have heq:(1+|src.t|+height)^(2*(JL+JR))=
        (1+|src.t|+height)^(JL+JR)*(1+|src.t|+height)^(JL+JR):=by
      rw [show 2*(JL+JR)=(JL+JR)+(JL+JR) by omega]
      exact pow_add _ _ _
    rw [heq]
    apply mul_le_mul
      (pow_le_pow_left₀ (by linarith) (by linarith [abs_nonneg src.t]) _)
      (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (by positivity) (by positivity)
  calc
    _ ≤ (Cp T*(CL+CR)*CenteredMomentSecondWindowBudget.profileMoment JL*
          CenteredMomentSecondWindowBudget.profileMoment JR)*(C₀+C₁+1)*
          (p.control (UL∪UR))^2*((1+height)^(JL+JR)*(1+|src.t|)^(JL+JR))*
          Z^(Mdecl+ell+εphysical)/(seed0.absNorm:ℝ) := by
      apply hmass.trans_eq
      dsimp [Fcap]
      ring
    _ ≤ _ := by gcongr

end SevenEighths.CenteredMomentEnergyCanonicalLowPhysical

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.NaturalLowPhysical. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowPhysical

open OAI.SevenEighths.CenteredMomentEnergyNaturalLowPhysical hiding actual_natural_low_physical

open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound

open CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands CenteredMomentInductionEnergy

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open OAI.SevenEighths.CenteredMomentEnergyNaturalLowSourceBound OAI.SevenEighths.CenteredMomentEnergyPositiveLowBandSource

open OAI.SevenEighths.CenteredMomentEnergyNaturalLowSourceBound

open OAI.SevenEighths.CenteredMomentEnergyPositiveLowBandSource

open OAI.SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

open OAI.SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighParameters OAI.SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighParameters

open OAI.SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageMargins OAI.SevenEighths.CenteredMomentEnergyFirstSourceParameters

open OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentEnergyFirstSourceParameters

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyNaturalInputMatches

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyNaturalInputMatches

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_natural_low_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤Mglobal)(hA:0≤A)(hB:0≤B)(hBm:0≤Bmask)
    (_hMp:0≤Mparent)(hMc:0≤Mchild)(hL:0≤Lgoal)(hLs:0≤Lslot)
    (hMA:Mparent≤A)(hready:readyBudget A Bmask≤B)
    (hκ:(3/4:ℝ)≤κ)
    (hκone:1 ≤ κ)(hε:0<ε)
    (hslot:Lslot≤mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤stageLoss Mglobal B ε k→0≤C₀→0≤C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0<a0:=OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0<lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0<r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLbase:0≤max Lgoal Mparent:=hL.trans (le_max_left _ _)
  have hLphys:0≤2*max Lgoal Mparent+r/4:=by positivity
  obtain ⟨U,J,hphysical⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalLowPhysical.actual_low_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (2*max Lgoal Mparent+r/4) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall  hκone N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=>aslot) (fun _=>bslot) (fun _=>hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b),
    eventually_scale_admission b (max Lgoal Mparent) (r/4) hLbase hr]
    with Z hZZ hfit hclipPow hscale
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0<max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlow
  let inp:=zeroSourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤N:=Fintype.card_le_of_injective (fun i:T=>i.val) Subtype.val_injective
  have hm:=(both_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂).2
  have hu:=hscale.2 T M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ
    hw hκsmall (hstate.trans (le_max_right _ _)) hcapacity
  have hg:max Lgoal Mparent≤2*max Lgoal Mparent+r/4:=by linarith
  have hu1:inp.X₁≤Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hu2:inp.X₂≤Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hp:=lower_product_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hlowV:Real.logb Z (volume inp)≤5*state.width/6:=
    (low_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ hZ hlow).2
  have hr:=OAI.SevenEighths.CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=>le_rfl) (fun _=>le_rfl) (fun _=>rfl) (fun _=>rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu1 hu2 hu.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl hlowV (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  have hv0:volume inp = volume (sourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂):=rfl
  rw [ht,hv0] at hh
  simpa only [map_one,Nat.cast_one,div_one,mul_assoc] using hh

end SevenEighths.CenteredMomentEnergyNaturalLowPhysical

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.NaturalLowStage. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowStage

open OAI.SevenEighths.CenteredMomentEnergyNaturalLowStage hiding actual_low_from_bands

open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound

open CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands CenteredMomentInductionEnergy

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open OAI.SevenEighths.CenteredMomentEnergyNaturalLowSourceBound OAI.SevenEighths.CenteredMomentEnergyPositiveLowBandSource

open OAI.SevenEighths.CenteredMomentEnergyNaturalLowSourceBound

open OAI.SevenEighths.CenteredMomentEnergyPositiveLowBandSource

open OAI.SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

open OAI.SevenEighths.CenteredMomentEnergyNaturalSourceAdmission

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighParameters OAI.SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighParameters

open OAI.SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageMargins OAI.SevenEighths.CenteredMomentEnergyFirstSourceParameters

open OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentEnergyFirstSourceParameters

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyNaturalInputMatches

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyNaturalInputMatches

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyNaturalLowPhysical OAI.SevenEighths.CenteredMomentEnergyReferenceLowBands

open OAI.SevenEighths.CenteredMomentEnergyNaturalLowPhysical hiding actual_natural_low_physical

open OAI.SevenEighths.CenteredMomentEnergyReferenceLowBands

open OAI.SevenEighths.CenteredMomentEnergyBandMonotonicity

open OAI.SevenEighths.CenteredMomentEnergyBandMonotonicity

theorem actual_low_from_bands
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)(hΦ:2≤bΦ)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot κ ε:ℝ)(k:ℕ)
    (hMg:0≤Mglobal)(hA:0≤A)(hB:0≤B)(hBm:0≤Bmask)
    (hMp:0≤Mparent)(hMc:0≤Mchild)(hL:0≤Lgoal)(hLs:0≤Lslot)
    (hMA:Mparent≤A)(hready:readyBudget A Bmask≤B)
    (hκ:(3/4:ℝ)≤κ)
    (hκone:1 ≤ κ)(hε:0<ε)
    (hslot:Lslot≤mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃Uout:Finset (ℕ×ℕ),∃Jout:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤stageLoss Mglobal B ε k→0≤C₀→0≤C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask Lgoal Lslot lo hi Mparent
        (physicalLoss Mglobal B ε k) κ Z η₀ Q Jout Uout (C*(C₀+C₁+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask Lgoal Mparent
        (physicalLoss Mglobal B ε k) Z Jout Uout (C*(C₀+C₁+1)) :=by
  let r:=reserve Mglobal B ε
  have hκ0:0≤κ:=by linarith
  have hr:0<r:=(bounds Mglobal B κ ε hMg hB hκ0 hε).2.2.2.1
  have hmarg:=margins Mglobal B κ ε hMg hB hκ0 hε k
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hbΦ:0<bΦ:=by linarith
  obtain ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,hentry⟩:=
    OAI.SevenEighths.CenteredMomentEnergyPositiveLowSourceControlled.actual_low_stages_from_physical (α:=α)
      M H hH W hW.continuous aslot bslot lo hi a b bΦ Mparent (r/4) (r/4)
      (2*amplification ε+1) haslot hWs hbslot ha hb hbΦ hMp (by positivity) (by positivity)
  obtain ⟨U,J,hphysical⟩:=actual_natural_low_physical (α:=α) M H hH W hW aslot bslot lo hi a b bΦ
    haslot hWs hbslot ha hb Mglobal A B Bmask Mparent Mchild Lgoal Lslot Mchild κ ε k
    hMg hA hB hBm hMp hMc hL hLs hMA hready hκ  hκone hε hslot hdrop Ψ degree S
  let Umerge:=S∪U
  let Jmerge:=degree+J
  have hS:S⊆Umerge:=Finset.subset_union_left
  have hU:U⊆Umerge:=Finset.subset_union_right
  have hdeg:degree≤Jmerge:=Nat.le_add_right _ _
  have hJ:J≤Jmerge:=Nat.le_add_left _ _
  have halower:a/max 1 b≤a:=by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
    nlinarith [le_max_left (1:ℝ) b]
  have hlen:Lgoal≤2*max Lgoal Mparent+r/4:=by
    have hh:=le_max_left Lgoal Mparent
    linarith
  refine ⟨insert (0,0) Umerge,Jmerge,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cp,hCp,hphys⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  let Cout:=Cfixed*(Cp+1)+1
  have hCout:0<Cout:=by dsimp [Cout];positivity
  refine ⟨Cout,hCout,?_⟩
  filter_upwards [hentry,hphys] with Z he hp
  refine ⟨hp.1,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
  have hzsmall:=zeroAt_transport (internalQ Q η₀)
    (a/max 1 b) b bΦ Bmask _ Mchild εchild Z
    (a/max 1 b) b 2 0 _ Mchild εchild degree degree S S C₀ C₀ hp.1.le
    le_rfl le_rfl hΦ hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₀ le_rfl hzero
  have hpsmall:=positiveAt_transport (α:=α) M H hH W bslot
    (a/max 1 b) b bΦ Bmask _ Lslot lo hi Mchild εchild κ Z
    (a/max 1 b) b 2 0 _ Mchild εchild η₀ Q degree degree S S C₁ C₁ hp.1.le
    le_rfl le_rfl hΦ hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₁ le_rfl hpos
  have hold:=positiveAt_transport (α:=α) M H hH W bslot
    (a/max 1 b) b bΦ Bmask _ Lslot lo hi Mchild εchild κ Z
    a b bΦ Bmask Lgoal Mchild (physicalLoss Mglobal B ε k) η₀ Q
    degree Jmerge S Umerge C₁ C₁ hp.1.le halower le_rfl le_rfl le_rfl hlen le_rfl
    (hell.trans hmarg.2.1) hdeg hS hC₁ le_rfl hpos
  have hm:=hp.2 εchild C₀ C₁ hell hC₀ hC₁ hzsmall hpsmall
  have hm':PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
      a b bΦ Bmask Lgoal Lslot Mchild Mparent κ (r/4) (physicalLoss Mglobal B ε k)
      Z ha Ψ η₀ Q Umerge Jmerge (Cp*(C₀+C₁+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hh:=hm T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hz:0≤Z:=zero_le_one.trans hp.1.le
    have hcontrol:=profile_control_mono p hU
    have hc0:=p.control_nonneg U
    have hheight1:1≤1+|t|+height:=by linarith [abs_nonneg t]
    apply hh.trans
    gcongr
  have hsave:-(2*amplification ε+1)≤physicalLoss Mglobal B ε k:=by
    have hs:0<amplification ε:=(bounds Mglobal B κ ε hMg hB hκ0 hε).1
    linarith [hmarg.1]
  have hout:=he.2 Bmask Lgoal Lslot Mchild κ (physicalLoss Mglobal B ε k) η₀ Q Umerge Jmerge
    (Cp*(C₀+C₁+1)) C₁ hκsmall (by positivity) hC₁ hmarg.2.2.1 hsave hold hm'
  have hC:Cfixed*(Cp*(C₀+C₁+1)+1)+C₁≤Cout*(C₀+C₁+1):=by
    dsimp [Cout]
    nlinarith [mul_nonneg hCfixed.le hC₀,mul_nonneg hCfixed.le hC₁]
  constructor
  · exact OAI.SevenEighths.CenteredMomentEnergyStageMonotonicity.positiveLowAt_transport (α:=α) M H hH W bslot
      a b bΦ Bmask Lgoal Lslot lo hi Mparent (physicalLoss Mglobal B ε k) κ Z
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) η₀ Q Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.1
  · exact OAI.SevenEighths.CenteredMomentEnergyStageMonotonicity.zeroLowAt_transport (internalQ Q η₀)
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) Z
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.2

end SevenEighths.CenteredMomentEnergyNaturalLowStage

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.WidthFloor. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyWidthFloor

open OAI.SevenEighths.CenteredMomentEnergyWidthFloor hiding actual_joint_floor

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule CenteredMomentFiniteProfileExceptional

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open QuadraticInitialBound

local notation "O"=>HeckeFamily.O

private lemma control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(h:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono h) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_joint_floor (Mcap B κ ε:ℝ)(hMcap:0≤Mcap)(hB:0≤B)
    (hκ0:0≤κ)(hε:0<ε)
    (W:ℝ→ℂ)(aslot bslot:ℝ)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (a b bΦ Bmask L lo hi:ℝ)(ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hmask:0≤Bmask)
    (hκ:1 ≤ κ):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧
      ∀η₀:Character,∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Q:Ideal O,Q≤M→
        ZeroAt (internalQ Q η₀) a b bΦ Bmask L (width Mcap B ε 0)
          (loss Mcap B ε 0) Z degree S Czero ∧
        PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L (mesh Mcap B κ ε) lo hi
          (width Mcap B ε 0) (loss Mcap B ε 0) κ Z η₀ Q degree S Cpositive:=by
  have hs:=bounds Mcap B κ ε hMcap hB hκ0 hε
  have hr:=hs.2.2.2.1
  have hm:=hs.2.2.2.2.1
  obtain ⟨Jzero,Szero,Czero,hCzero,hzero⟩:=exists_zero_floor
    a b bΦ Bmask (reserve Mcap B ε) ha hb hbΦ hmask hr
  obtain ⟨Jpositive,Spositive,Cpositive,hCpositive,hpositive⟩:=exists_positive_bottom (α:=α)
    M H hH W aslot bslot haslot hWs hW a b bΦ Bmask L (mesh Mcap B κ ε) lo hi
      (reserve Mcap B ε) κ ha hb hbΦ hmask hr hm.le  hκ
  refine ⟨Jzero+Jpositive,Szero∪Spositive,Czero,Cpositive,hCzero,hCpositive,?_⟩
  intro η₀
  filter_upwards [hpositive η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Q hQM
  rw [width_zero,loss_zero]
  constructor
  · intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ _ _
    have hh:=hzero (internalQ Q η₀) Z hZ.1.le s hQ hwidth p t X₁ X₂ hX₁ hX₂
    have hp:=control_mono p (Finset.subset_union_left (s₁:=Szero) (s₂:=Spositive))
    have hpn:=p.control_nonneg Szero
    have hpU:=p.control_nonneg (Szero∪Spositive)
    have hd:=diagonalControl_nonneg s.radial.profile
    have ht:(1+‖t‖)^Jzero≤(1+‖t‖)^(Jzero+Jpositive):=
      pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Nat.le_add_right _ _)
    apply hh.trans
    gcongr
    exact Real.rpow_nonneg (zero_le_one.trans hZ.1.le) _
  · intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hwidth
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap
    have hh:=hZ.2 Q hQM T θ w σ v t height hw hwL hσlo hσhi hheight hv
      s hQ hwidth p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap
    have hp:=control_mono p (Finset.subset_union_right (s₁:=Szero) (s₂:=Spositive))
    have hpn:=p.control_nonneg Spositive
    have hpU:=p.control_nonneg (Szero∪Spositive)
    have hd:=diagonalControl_nonneg s.radial.profile
    have ht:(1+|t|+height)^Jpositive≤(1+|t|+height)^(Jzero+Jpositive):=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (Nat.le_add_left _ _)
    apply hh.trans
    gcongr
    exact Real.rpow_nonneg (zero_le_one.trans hZ.1.le) _

end SevenEighths.CenteredMomentEnergyWidthFloor

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CappedWidthInduction. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyCappedWidthInduction

open OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction hiding certified_floor

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule OAI.SevenEighths.CenteredMomentEnergyWidthRanges

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyWidthRanges

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule OAI.SevenEighths.CenteredMomentEnergyBandMonotonicity

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyBandMonotonicity

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyWidthFloor CenteredMomentFiniteProfileExceptional

open OAI.SevenEighths.CenteredMomentEnergyWidthFloor hiding actual_joint_floor

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

local notation "O"=>HeckeFamily.O

open OAI.SevenEighths.CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)

open OAI.SevenEighths.CenteredMomentEnergyWidthInduction

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem certified_floor (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (ha:0<a)(hb:0≤b)(hrad:0<radial)(hmask:0≤Bmask)(hMcap:0≤Mcap)
    (hκ0:0≤κ)(hε:0<ε)
    (hκ:1 ≤ κ):
    OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε 0:=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have ha0:=lowerAt_pos a b Mcap ε ha 0
  obtain ⟨degree,S,Czero,Cpositive,hCzero,hCpositive,hfloor⟩:=
    actual_joint_floor (α:=α) M H hH Mcap Bs κ ε hMcap hBs hκ0 hε W aslot bslot
      haslot hWs hW (lowerAt a b Mcap ε 0) b radial Bmask (lengthAt Mcap Bmask L ε 0)
      lo hi ha0 hb hrad hmask  hκ
  refine ⟨degree,S,?_⟩
  intro η₀ Q hQM _ _ _
  refine ⟨Czero,Cpositive,hCzero,hCpositive,?_⟩
  filter_upwards [hfloor η₀] with Z hZ
  have hh:=hZ.2 Q hQM
  have hloss:loss Mcap Bs ε 0≤stageLoss Mcap Bs ε 0:=by
    unfold stageLoss
    linarith
  refine ⟨hZ.1,?_,?_⟩
  · exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Czero Czero hZ.1.le le_rfl le_rfl le_rfl le_rfl
      le_rfl (bandWidth_le_schedule Mcap Bs ε 0) hloss le_rfl (Finset.Subset.refl _) hCzero.le le_rfl hh.1
  · exact positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cpositive Cpositive hZ.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl (bandWidth_le_schedule Mcap Bs ε 0) hloss le_rfl (Finset.Subset.refl _)
      hCpositive.le le_rfl hh.2

end SevenEighths.CenteredMomentEnergyCappedWidthInduction

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CappedLowStage. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyCappedLowStage

open OAI.SevenEighths.CenteredMomentEnergyCappedLowStage hiding actual_capped_low

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCappedWidthInduction OAI.SevenEighths.CenteredMomentEnergyWidthInduction

open OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction hiding certified_floor

open OAI.SevenEighths.CenteredMomentEnergyWidthInduction

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule OAI.SevenEighths.CenteredMomentEnergyWidthRanges

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyWidthRanges

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentEnergyBandMonotonicity OAI.SevenEighths.CenteredMomentEnergyReferenceLowBands

open OAI.SevenEighths.CenteredMomentEnergyBandMonotonicity

open OAI.SevenEighths.CenteredMomentEnergyReferenceLowBands

open OAI.SevenEighths.CenteredMomentEnergyCappedRequests OAI.SevenEighths.CenteredMomentEnergySourceCapSchedule

open OAI.SevenEighths.CenteredMomentEnergyCappedRequests

open OAI.SevenEighths.CenteredMomentEnergySourceCapSchedule

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_capped_low
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hW:ContDiff ℝ ∞ W)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hbslot:0≤bslot)
    (ha:0<a)(hb:0≤b)(hrad:2≤radial)(hmask:0≤Bmask)(hMcap:0≤Mcap)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε)
    (hκone:1 ≤ κ)(k:ℕ)(hk:k<count Mcap ε)
    (hold:OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε k):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
        PositiveLowAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q J U C ∧
        ZeroLowAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z J U C :=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Ag:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let Lreq:=requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1))
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hRange:=range_nonneg Mcap Bmask L hMcap hmask (count Mcap ε)
  have hAg:0≤Ag:=by dsimp [Ag];positivity
  have hMp:0≤Mp:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε (k+1)
  have hMc:0≤Mc:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε k
  have hMpCap:Mp≤Mcap:=bandWidth_le Mcap Bs ε (k+1)
  have hMpAg:Mp≤Ag:=by dsimp [Ag];linarith
  have hLnext:0≤lengthAt Mcap Bmask L ε (k+1):=
    range_nonneg Mcap Bmask L hMcap hmask _
  have hLreq:0≤Lreq:=(request_bounds Mcap Bmask _ hMcap hmask hLnext).1
  have hκ0:0≤κ:=by linarith
  have hbounds:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have hmesh:0≤fineMesh Mcap Bmask L κ ε:=hbounds.2.2.2.2.1.le
  have hr:0<reserve Mcap Bs ε:=hbounds.2.2.2.1
  have hr4:reserve Mcap Bs ε/4≤1:=by
    have hh:reserve Mcap Bs ε≤amplification ε/100:=min_le_left _ _
    have hs:=hbounds.2.1
    linarith
  have hready:OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission.readyBudget Ag Bmask≤Bs:=
    readyBudget_le_schedule Mcap Bmask L ε Ag Bmask hMcap hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤Mc:=parent_drop Mcap Bs ε hε k
  have hlength:2*max Lreq Mp+reserve Mcap Bs ε/4≤lengthAt Mcap Bmask L ε k:=
    previous_admits Mcap Bmask L ε Mp (reserve Mcap Bs ε/4) hMcap hmask hMpCap hr4 k hk
  have hsupport:=child_support a b Mcap ε k hk
  obtain ⟨degree,S,hold⟩:=hold
  obtain ⟨U,J,hstage⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyNaturalLowStage.actual_low_from_bands
    (α:=α) M H hH W hW aslot bslot lo hi (lowerAt a b Mcap ε (k+1)) b radial
    haslot hWs hbslot (lowerAt_pos a b Mcap ε ha (k+1)) hb hrad
    Mcap Ag Bs Bmask Mp Mc Lreq (fineMesh Mcap Bmask L κ ε) κ ε k
    hMcap hAg hBs hmask hMp hMc hLreq hmesh hMpAg hready hκ  hκone hε
    le_rfl hdrop degree S
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz,Cp,hCz,hCp,hold⟩:=hold η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cs,hCs,hstage⟩:=hstage η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cs*(Cz+Cp+1),by positivity,?_⟩
  filter_upwards [hold,hstage] with Z hold hs
  have hz : ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
      (lengthAt Mcap Bmask L ε k) Mc (stageLoss Mcap Bs ε k) Z degree S Cz := hold.2.1
  have hp : PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
      (lengthAt Mcap Bmask L ε k) (fineMesh Mcap Bmask L κ ε) lo hi Mc
      (stageLoss Mcap Bs ε k) κ Z η₀ Q degree S Cp := hold.2.2
  rw [hsupport] at hz hp
  have hz':ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) Mc (stageLoss Mcap Bs ε k) Z degree S Cz:=
    zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Cz Cz hold.1.le le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl
      le_rfl (Finset.Subset.refl _) hCz.le le_rfl hz
  have hp':PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) (fineMesh Mcap Bmask L κ ε) lo hi Mc
      (stageLoss Mcap Bs ε k) κ Z η₀ Q degree S Cp:=
    positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cp Cp hold.1.le
      le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hp
  exact ⟨hs.1,hs.2 (stageLoss Mcap Bs ε k) Cz Cp le_rfl hCz.le hCp.le hz' hp'⟩

end SevenEighths.CenteredMomentEnergyCappedLowStage

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.PositiveHighPhysical. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighPhysical

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighPhysical hiding actual_positive_high_physical

open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound

open CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands CenteredMomentInductionEnergy

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighSource OAI.SevenEighths.CenteredMomentEnergyPositiveHighSourceBound

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighSource

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighSourceBound

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighParameters OAI.SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighParameters

open OAI.SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageMargins OAI.SevenEighths.CenteredMomentEnergyFirstSourceParameters

open OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentEnergyFirstSourceParameters

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyNaturalInputMatches

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyNaturalInputMatches

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_positive_high_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hb:0≤b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤Mglobal)(hA:0≤A)(hB:0≤B)(hBm:0≤Bmask)
    (_hMp:0≤Mparent)(hMc:0≤Mchild)(hL:0≤Lgoal)(hLs:0≤Lslot)
    (hMA:Mparent≤A)(hready:readyBudget A Bmask≤B)
    (hκ:(3/4:ℝ)≤κ)
    (hκone:1 ≤ κ)(hε:0<ε)
    (hslot:Lslot≤mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤stageLoss Mglobal B ε k→0≤C₀→0≤C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalHighAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0<a0:=OAI.SevenEighths.CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0<lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0<r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLphys:0≤max Lgoal Mparent:=hL.trans (le_max_left _ _)
  obtain ⟨U,J,hphysical⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalHighPhysical.actual_high_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (max Lgoal Mparent) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall  hκone N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=>aslot) (fun _=>bslot) (fun _=>hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b)]
    with Z hZZ hfit hclipPow
  have hZ:1<Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0<max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlarge
  dsimp only
  intro hfour
  let inp:=balancedInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤N:=Fintype.card_le_of_injective (fun i:T=>i.val) Subtype.val_injective
  have hm:=balanced_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hu:=four_upper_scales M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ κ (max Lgoal Mparent)
    hZ hw hκ hcapacity (hstate.trans (le_max_right _ _))
  have hp:=fixed_lower_product M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hr:=OAI.SevenEighths.CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=>le_rfl) (fun _=>le_rfl) (fun _=>rfl) (fun _=>rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl le_rfl hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  rw [ht] at hh
  dsimp only [inp,r] at hh
  have hN1:((1:Ideal O).absNorm:ℝ)=1:=by norm_num
  simpa only [hN1,div_one,mul_assoc] using hh

end SevenEighths.CenteredMomentEnergyPositiveHighPhysical

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.NaturalHighStage. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalHighStage

open OAI.SevenEighths.CenteredMomentEnergyNaturalHighStage hiding actual_high_stage

open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound

open CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands CenteredMomentInductionEnergy

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighSource OAI.SevenEighths.CenteredMomentEnergyPositiveHighSourceBound

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighSource

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighSourceBound

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighParameters OAI.SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighParameters

open OAI.SevenEighths.CenteredMomentEnergyPositiveBalancedAdmission

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageMargins OAI.SevenEighths.CenteredMomentEnergyFirstSourceParameters

open OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentEnergyFirstSourceParameters

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyNaturalInputMatches

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyNaturalInputMatches

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_high_stage
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤bslot)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hrho:0<rho)(hMg:0≤Mglobal)(hA:0≤A)(hB:0≤B)(hBm:0≤Bmask)
    (hMp:0≤Mparent)(hMc:0≤Mchild)(hL:0≤Lgoal)(hLs:0≤Lslot)
    (hMA:Mparent≤A)(hready:readyBudget A Bmask≤B)
    (hκ:(3/4:ℝ)≤κ)
    (hκone:1 ≤ κ)(hε:0<ε)
    (hslot:Lslot≤mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(lowDegree:ℕ)(Slow:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁ Clow:ℝ,εchild≤stageLoss Mglobal B ε k→0≤C₀→0≤C₁→0≤Clow→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      OAI.SevenEighths.CenteredMomentEnergyReferenceLowBands.PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask
        (Mparent+Bmask+rho/100) Lslot lo hi Mparent (physicalLoss Mglobal B ε k) κ Z η₀ Q
        lowDegree Slow Clow→
      PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask Lgoal Lslot lo hi rho Mparent
        (reflectedLoss Mglobal B ε k) κ Z η₀ Q J U (C*(C₀+C₁+Clow+1)) := by
  let r:=reserve Mglobal B ε
  have hκ0:0≤κ:=by linarith
  have hb:0≤b:=zero_le_one.trans hhi
  have hr:0<r:=(bounds Mglobal B κ ε hMg hB hκ0 hε).2.2.2.1
  have hr4:0<r/4:=by positivity
  have hs:0<amplification ε:=(bounds Mglobal B κ ε hMg hB hκ0 hε).1
  obtain ⟨Ψ,hΨs,hΨn,hstage⟩:=actual_high_stage_from_physical (α:=α) M H hH
    W hW.continuous aslot bslot lo hi a b bΦ rho r Mparent Bmask (r/4) (r/4)
    (2*amplification ε+1) haslot hWs hbslot ha hlo hhi hbΦ hrho hr hMp hBm hr4 hr4
  obtain ⟨Up,Jp,hphysical⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyPositiveHighPhysical.actual_positive_high_physical
    (α:=α) M H hH W hW aslot bslot lo hi a b bΦ haslot hWs hbslot ha hb
    Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε k hMg hA hB hBm hMp hMc hL hLs
    hMA hready hκ  hκone hε hslot hdrop Ψ degree S
  obtain ⟨J,U,Cf,hCf,hstageZ⟩:=hstage lowDegree Slow Jp Up
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cp,hCp,hphysZ⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cf*(Cp+1),by positivity,?_⟩
  filter_upwards [hstageZ,hphysZ] with Z hstageNow hphysicalNow
  refine ⟨hphysicalNow.1,?_⟩
  intro εchild C₀ C₁ Clow hchild hC₀ hC₁ hClow hzero hpos hlow
  have hp:=hphysicalNow.2 εchild C₀ C₁ hchild hC₀ hC₁ hzero hpos
  have hm:=margins Mglobal B κ ε hMg hB hκ0 hε k
  have hmass:0≤Cp*(C₀+C₁+1):=by positivity
  have hh:=hstageNow.2 Lgoal Lslot κ (physicalLoss Mglobal B ε k)
    (physicalLoss Mglobal B ε k) (reflectedLoss Mglobal B ε k) η₀ Q
    Clow (Cp*(C₀+C₁+1)) hκ hm.1.le hClow hmass
    (by exact le_rfl) hm.2.2.2.1 (hm.2.2.1.trans hm.2.2.2.1)
    (by have hpos:=hm.1.le.trans hm.2.2.2.1;linarith only [hpos,hs]) hlow hp
  have hconst:Cf*(Clow+Cp*(C₀+C₁+1)+1)≤(Cf*(Cp+1))*(C₀+C₁+Clow+1):=by
    have hh:0≤Cp*Clow:=mul_nonneg hCp.le hClow
    nlinarith only [mul_nonneg hCf.le hh,mul_nonneg hCf.le hC₀,mul_nonneg hCf.le hC₁]
  intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hslo hsupper
    p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂ hcapacity hlarge
  apply (hh T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hslo hsupper
    p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂ hcapacity hlarge).trans
  have hd:=diagonalControl_nonneg state.radial.profile
  have hp0:=p.control_nonneg U
  have hz:0≤Z:=zero_le_one.trans hphysicalNow.1.le
  gcongr

end SevenEighths.CenteredMomentEnergyNaturalHighStage

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.ZeroGrowthPhysical. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthPhysical

open OAI.SevenEighths.CenteredMomentEnergyZeroGrowthPhysical hiding actual_growth_physical

open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSecondHeightFamily

open CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy

open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

open OAI.SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex CenteredMomentSourceInputReindex

open OAI.SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalReindex

open OAI.SevenEighths.CenteredMomentEnergyZeroBalancedAdmission OAI.SevenEighths.CenteredMomentEnergyZeroBalancedDictionary

open OAI.SevenEighths.CenteredMomentEnergyZeroBalancedAdmission

open OAI.SevenEighths.CenteredMomentEnergyZeroBalancedDictionary

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyFirstSourceParameters OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyFirstSourceParameters

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCanonicalHighPhysical OAI.SevenEighths.CenteredMomentEnergyZeroGrowthSource

open OAI.SevenEighths.CenteredMomentEnergyCanonicalHighPhysical hiding actual_high_physical

open OAI.SevenEighths.CenteredMomentEnergyZeroGrowthSource

open OAI.SevenEighths.CenteredMomentEnergyStageMargins ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentEnergyFirstGaussianProfileWeights

open OAI.SevenEighths.CenteredMomentFirstAmplifiedFourCoefficients

open OAI.SevenEighths.CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceReduction

open OAI.SevenEighths.CenteredMomentSecondInputCapacitySource

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_growth_physical
    (Wslot:ℝ→ℂ)(aslot bslot Lslot lo hi κ a b bΦ Bmask Lgoal Lchild Mparent Mchild
      Mschedule Bschedule ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hLs:0≤Lslot)(hκ:(3/4:ℝ)≤κ)
    (hκone:1 ≤ κ)
    (ha:0<a)(hb:0≤b)(hBmask:0≤Bmask)(hLgoal:0≤Lgoal)(hLchild:0≤Lchild)
    (hMparent:0≤Mparent)(hMchild:0≤Mchild)(hMschedule:0≤Mschedule)(hBschedule:0≤Bschedule)
    (hε:0<ε)(hcap: max Mparent (2*Lgoal)≤Lchild)
    (hready:readyBudget (max Mparent (2*Lgoal)) Bmask≤Bschedule)
    (hdrop:Mparent-amplification ε/2≤Mchild)
    (Ψ:𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(k:ℕ)(εchild C₀ C₁ rho:ℝ),εchild≤stageLoss Mschedule Bschedule ε k→
      0≤C₀→0≤C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 Lchild Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 Lchild Lslot lo hi
        Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalGrowthAt (internalQ Q η₀) a b bΦ Bmask Lgoal rho Mparent
        (reserve Mschedule Bschedule ε/4) (physicalLoss Mschedule Bschedule ε k)
        Z ha Ψ Uprofile Jheight (C*(C₀+C₁+1)):=by
  let A:=max Mparent (2*Lgoal)
  let r:=reserve Mschedule Bschedule ε
  have hA:0≤A:=hMparent.trans (le_max_left _ _)
  obtain ⟨hsigma,hsigma1,hr,hxiSigma,hxi1,hes,hes1,hem,hmesh,hmeshEta,heta0,heta,hSaving,hSeed⟩:=
    parameter_gates Mschedule A Bschedule κ ε hMschedule hA hBschedule hκ hε
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have ha2:0<a^2:=sq_pos_of_pos ha
  obtain ⟨U,J,hphysical⟩:=actual_high_physical (α:=α) M H hH
    Wslot aslot bslot Mchild Lslot (r/4) lo hi κ a b 1
    (maskEpsilon Mschedule Bschedule ε) (by norm_num) hem ha hb
    Lchild hLchild degree S haslot hWs hW hMchild hLs hr hκsmall  hκone
    0 1 1 (a^2) (r/4) (by norm_num) (by norm_num) ha2 hr
    (fun _=>1) (fun _=>1) (fun _=>by norm_num)
    (sourceEpsilon Mschedule A Bschedule ε) (r/4) (r/4) (A+1) (r/4)
    (2*amplification ε+1) hes hr hr hr
    (amplification ε) hsigma hxiSigma A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBmask heta hr hsigma1 hxi1 hr hes1 le_rfl (fun _=>Ψ) (r/4) (a*a)
    hr (mul_pos ha ha)
  have hfit:=eventually_actual_four_fit Mschedule A Bmask Bschedule κ ε
    hMschedule hA hBmask hBschedule hready hκ hε
  have hclip:∀ᶠZ:ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    filter_upwards [eventually_gt_atTop (1:ℝ),
      (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<2*(r/4) by linarith)))
        (max 1 b*max 1 b)] with Z hZ hz
    exact ⟨hZ,(Real.logb_le_iff_le_rpow hZ (mul_pos
      (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _)))).mpr hz⟩
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Zbase,hZbase,hphysical⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Znum,hZnum⟩:=Filter.eventually_atTop.mp (hfit.and hclip)
  refine ⟨C,hC,max Zbase Znum,hZbase.trans_le (le_max_left _ _),?_⟩
  intro Z hZZ k εchild C₀ C₁ rho hchild hC₀ hC₁ hzero hpos
  have hZbaseLe:Zbase≤Z:=(le_max_left _ _).trans hZZ
  have hn:=hZnum Z ((le_max_right _ _).trans hZZ)
  have hZ:1<Z:=hn.1.1
  intro s hQ hsLower hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hlarge
  dsimp only
  intro hfour
  let src:=emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α
  let θ:(∅:Finset α)→RayQuotient.Characters M H:=fun i=>isEmptyElim i
  have hmatch:OAI.SevenEighths.CenteredMomentAllocatedRayDictionary.Matches M H hH src η₀ θ
      (fun _=>0) (fun _=>0) (fun _=>0) Wslot bslot Z:=by
    constructor <;> intro i <;> exact isEmptyElim i
  have hupper:=four_upper_scales s p ha t X₁ X₂ hX₁ hX₂ Mparent Lgoal hZ hLgoal hs hc₁ hc₂
  have hu:Z^A≤Z^Lchild:=Real.rpow_le_rpow_of_exponent_le hZ.le hcap
  have hgate:=declared_capacity s p ha t X₁ X₂ hX₁ hX₂ hZ
  have hdecl:=declared_capacity_upper s X₁ X₂ Mparent Lgoal hZ hLgoal hs hc₁ hc₂
  have hK:=OAI.SevenEighths.CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  have hbound:=hphysical ∅ θ Z hZbaseLe εchild C₀ C₁ hC₀ hC₁ hzero hpos
    (fun _=>0) (fun _=>0) (fun _=>0) 0 (mesh Mschedule Bschedule κ ε) hmesh.le
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i) (by norm_num)
    (fun i=>isEmptyElim i) src hmatch
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i) (by simp) le_rfl le_rfl
    hb hb (le_max_right _ _) (le_max_right _ _) (by simp)
    s.puncture 1 s.puncture_ne_zero s.puncture_bound squarefree_one one_ne_zero
    s.radial.scale hK.1 p rfl rfl
    (hupper.1.trans hu) (hupper.2.1.trans hu) (hupper.2.2.1.trans hu) (hupper.2.2.2.trans hu)
    (max s.width (length Z X₁+length Z X₂)) s.width (r/4)
    (columnLoss Mschedule Bschedule ε k) hr.le hdecl
    (by
      change length Z X₁+length Z X₂+6*κ*(∑i:(∅:Finset α),(0:ℝ))≤_
      simpa only [Finset.sum_const_zero,mul_zero,add_zero] using
        le_max_right s.width (length Z X₁+length Z X₂))
    (hgate.2.1.trans (le_max_left _ _)) hgate.2.1 (by linarith)
    hn.2.2 (by simp [lowerFactor]) (le_max_left _ _)
    hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hn.1.2 k εchild hchild)
  rw [show physicalMass src s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z (r/4)=
      physicalMass (OAI.SevenEighths.CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)
        s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z (r/4) from
        empty_balanced_mass s p ha t X₁ X₂ hX₁ hX₂ _ _ _ _ _ _ _ _] at hbound
  rw [show volume src=X₁*X₂ from empty_balanced_volume s p ha t X₁ X₂ hX₁ hX₂] at hbound
  have heq:max s.width (length Z X₁+length Z X₂)+columnLoss Mschedule Bschedule ε k+r/4=
      max s.width (length Z X₁+length Z X₂)+physicalLoss Mschedule Bschedule ε k:=by
    dsimp only [r]
    rw [add_assoc,columnLoss_physical]
  simpa only [map_one,Nat.cast_one,div_one,add_zero,
    show (src).t=t from rfl,heq] using hbound

end SevenEighths.CenteredMomentEnergyZeroGrowthPhysical

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.NaturalZeroStage. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalZeroStage

open OAI.SevenEighths.CenteredMomentEnergyNaturalZeroStage hiding actual_zero_stage

open HeckeFamily ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands CenteredMomentEnergyState

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open OAI.SevenEighths.CenteredMomentEnergyReferenceLowBands OAI.SevenEighths.CenteredMomentEnergyBandMonotonicity

open OAI.SevenEighths.CenteredMomentEnergyReferenceLowBands

open OAI.SevenEighths.CenteredMomentEnergyBandMonotonicity

open OAI.SevenEighths.CenteredMomentEnergyStageMonotonicity OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageMonotonicity

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_zero_stage
    (W:ℝ→ℂ)(aslot bslot Lslot lo hi κ a b bΦ Bmask Lgoal Mparent Mchild
      Mschedule Bschedule ε rho:ℝ)(k:ℕ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hLs:0≤Lslot)(hκ:(3/4:ℝ)≤κ)
    (hκone:1 ≤ κ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:2≤bΦ)(hBmask:0≤Bmask)(_hLgoal:0≤Lgoal)
    (hMparent:0≤Mparent)(hMchild:0≤Mchild)(hMschedule:0≤Mschedule)(hBschedule:0≤Bschedule)
    (hε:0<ε)(hrho:0<rho)(hrhoChild:rho≤Mchild)
    (hdrop:Mparent-amplification ε/2≤Mchild):
    ∃d Lgrow Llow:ℝ,0<d ∧ d≤1 ∧ 0<Lgrow ∧ Lgoal≤Lgrow ∧
      Lgrow=max Lgoal (Mparent+Bmask+2*d)+1 ∧
      Llow=max Lgrow (Mparent+Bmask+rho/100) ∧
      Llow≤max Lgoal (Mparent+Bmask+rho/100+2)+1 ∧
    ∀Lchild:ℝ,0≤Lchild→max Mparent (2*Lgrow)≤Lchild→
      readyBudget (max Mparent (2*Lgrow)) Bmask≤Bschedule→
    ∀degree degreeLow:ℕ,∀S Slow:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),
    ∀η₀:Character,∀Q:Ideal O,Q≤M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀εchild C₀ C₁ Clow:ℝ,εchild≤stageLoss Mschedule Bschedule ε k→
      0≤C₀→0≤C₁→0≤Clow→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask Lchild Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask Lchild Lslot lo hi
        Mchild εchild κ Z η₀ Q degree S C₁→
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask Llow Mparent
        (physicalLoss Mschedule Bschedule ε k) Z degreeLow Slow Clow→
      ZeroAt (internalQ Q η₀) a b bΦ Bmask Lgoal Mparent
        (stageLoss Mschedule Bschedule ε (k+1)) Z J U (C*(Clow+C₀+C₁+1)):=by
  let r:=reserve Mschedule Bschedule ε
  have hκ0:0≤κ:=by linarith
  have hr:0<r:=(bounds Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε).2.2.2.1
  have hb:0≤b:=by linarith
  have hrad:0<bΦ:=by linarith
  obtain ⟨d,Lgrow,hd,hd1,hLg,hgoal,hLexact,hLupper,hsharp⟩:=
    OAI.SevenEighths.CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded
      a b bΦ r Mparent Bmask Lgoal ha hlo hhi hrad hr hMparent hBmask
  let Llow:=max Lgrow (Mparent+Bmask+rho/100)
  refine ⟨d,Lgrow,Llow,hd,hd1,hLg,hgoal,hLexact,rfl,?_,?_⟩
  · apply max_le
    · apply hLupper.trans
      exact add_le_add (max_le_max (le_refl Lgoal)
        (show Mparent+Bmask+2≤Mparent+Bmask+rho/100+2 by linarith only [hrho])) (le_refl (1:ℝ))
    · have hh:=le_max_right Lgoal (Mparent+Bmask+rho/100+2)
      linarith
  intro Lchild hLc hcap hready degree degreeLow S Slow
  obtain ⟨Ψ,hsΨ,hnΨ,hgrowth⟩:=
    OAI.SevenEighths.CenteredMomentEnergyZeroGrowthSourceControlled.actual_growth_from_physical
      a b bΦ rho r Mparent Bmask (2*Lgrow) Lgrow (r/4) (r/4) (2*amplification ε+1)
      ha hlo hhi hrad hrho hr hMparent hBmask (by positivity) le_rfl (by positivity) (by positivity)
  obtain ⟨Smass,Jmass,hphysical⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyZeroGrowthPhysical.actual_growth_physical (α:=α) M H hH
      W aslot bslot Lslot lo hi κ a b bΦ Bmask Lgrow Lchild Mparent Mchild Mschedule Bschedule ε
      haslot hWs hW hLs hκ  hκone ha hb hBmask hLg.le hLc hMparent hMchild
      hMschedule hBschedule hε hcap hready hdrop Ψ degree S
  obtain ⟨Jgrowth,Ugrowth,Cgrowth,hCg,hgrowth⟩:=hgrowth (degree+degreeLow) (S∪Slow) Jmass Smass
  obtain ⟨J,U,Csharp,hCs,hsharp⟩:=hsharp Ugrowth
  refine ⟨J,U,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cmass,hCm,Zmass,hZm,hmass⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  let C:=Csharp*(Cgrowth*(Cmass+2)+1)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_ge_atTop Zmass,hgrowth,hsharp] with Z hZmZ hg hs
  have hZ:1<Z:=hZm.trans_le hZmZ
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ Clow hchild hC₀ hC₁ hClow hz hp hl
  have hmarg:=margins Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε k
  have hpLoss:0≤physicalLoss Mschedule Bschedule ε k:=hmarg.1.le
  have hrLoss:0≤reflectedLoss Mschedule Bschedule ε k:=hpLoss.trans hmarg.2.2.2.1
  have hlength:Lgrow≤Lchild:=by linarith [le_max_right Mparent (2*Lgrow)]
  have hap:a/max 1 b≤a:=div_le_self ha.le (le_max_left _ _)
  have hzero:=zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ 2 0 _ _ _
    degree degree S S C₀ C₀ hZ.le le_rfl le_rfl hbΦ hBmask le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) hC₀ le_rfl hz
  have hpositive:=positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
    _ _ 2 0 _ _ _ η₀ Q degree degree S S C₁ C₁ hZ.le
    le_rfl le_rfl hbΦ hBmask le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₁ le_rfl hp
  have hmassNow:=hmass Z hZmZ k εchild C₀ C₁ rho hchild hC₀ hC₁ hzero hpositive
  have hprevious:=zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z a b bΦ Bmask Lgrow rho
    (reflectedLoss Mschedule Bschedule ε k) degree (degree+degreeLow) S (S∪Slow) C₀ C₀
    hZ.le hap le_rfl le_rfl le_rfl hlength hrhoChild
    (hchild.trans (hmarg.2.1.trans hmarg.2.2.2.1)) (Nat.le_add_right _ _)
    Finset.subset_union_left hC₀ le_rfl hz
  have hlow:=zeroLowAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    degreeLow (degree+degreeLow) Slow (S∪Slow) Clow Clow hZ.le
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_add_left _ _)
    Finset.subset_union_right hClow le_rfl hl
  have hgrowthNow:=hg.2 (physicalLoss Mschedule Bschedule ε k)
    (physicalLoss Mschedule Bschedule ε k) (reflectedLoss Mschedule Bschedule ε k)
    (internalQ Q η₀) Clow (Cmass*(C₀+C₁+1)) C₀ hpLoss hClow (by positivity) hC₀
    (by unfold reflectedLoss;exact le_rfl) hmarg.2.2.2.1
    (hmarg.2.2.1.trans hmarg.2.2.2.1)
    (by have hh:= (bounds Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε).1
        linarith only [hrLoss,hh]) hprevious hlow hmassNow
  have hfinal:=hs.2 (reflectedLoss Mschedule Bschedule ε k) (internalQ Q η₀) Jgrowth
    (Cgrowth*(Clow+Cmass*(C₀+C₁+1)+C₀+1)) hrLoss (by positivity) hgrowthNow
  rw [reflected_then_zero] at hfinal
  have hfront:Csharp*(Cgrowth*(Clow+Cmass*(C₀+C₁+1)+C₀+1)+1)≤C*(Clow+C₀+C₁+1):=by
    have hinner:Clow+Cmass*(C₀+C₁+1)+C₀+1≤(Cmass+2)*(Clow+C₀+C₁+1):=by
      nlinarith [mul_nonneg hCm.le hClow]
    calc
      _≤Csharp*(Cgrowth*((Cmass+2)*(Clow+C₀+C₁+1))+(Clow+C₀+C₁+1)):=by
        gcongr
        linarith
      _=_:=by dsimp [C];ring
  exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    J J U U _ _ hZ.le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) (by positivity) hfront hfinal

end SevenEighths.CenteredMomentEnergyNaturalZeroStage

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CappedAnalyticSuccessor. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

open Filter

namespace SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessor

open OAI.SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessor hiding actual_successor

open HeckeFamily CenteredMomentEnergyState ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyBands

open OAI.SevenEighths.CenteredMomentEnergyBands hiding exists_positive_bottom

open OAI.SevenEighths.CenteredMomentEnergyReferenceLowBands OAI.SevenEighths.CenteredMomentEnergyPositiveHighBound

open OAI.SevenEighths.CenteredMomentEnergyReferenceLowBands

open OAI.SevenEighths.CenteredMomentEnergyPositiveHighBound

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule OAI.SevenEighths.CenteredMomentEnergyWidthRanges

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyWidthRanges

open OAI.SevenEighths.CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)

open OAI.SevenEighths.CenteredMomentEnergyWidthInduction

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCappedWidthInduction

open OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction hiding certified_floor

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentEnergyStageReserveSchedule

open OAI.SevenEighths.CenteredMomentEnergyStageMargins

open OAI.SevenEighths.CenteredMomentEnergyBandMonotonicity OAI.SevenEighths.CenteredMomentEnergyStageMonotonicity

open OAI.SevenEighths.CenteredMomentEnergyBandMonotonicity

open OAI.SevenEighths.CenteredMomentEnergyStageMonotonicity

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission OAI.SevenEighths.CenteredMomentEnergyCappedRequests

open OAI.SevenEighths.CenteredMomentEnergyFirstLiveAdmission

open OAI.SevenEighths.CenteredMomentEnergyCappedRequests

open OAI.SevenEighths.CenteredMomentEnergySourceCapSchedule ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentNaturalFixedRaySource

open OAI.SevenEighths.CenteredMomentEnergySourceCapSchedule

open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource hiding natural_character_slot_bound natural_ray_slots_uniform natural_relative_slot_bound

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem actual_successor
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hrad:2≤radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ:(3/4:ℝ)≤κ)(hε:0<ε)
    (hκone:1 ≤ κ)
    (k:ℕ)(hk:k<count Mcap ε)
    (hold:OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k):
    OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let ac:=lowerAt a b Mcap ε (k+1)
  let Lc:=lengthAt Mcap Bmask L ε (k+1)
  let Lp:=lengthAt Mcap Bmask L ε k
  let Lreq:=requestLength Mcap Bmask Lc
  let A:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let r:=reserve Mcap Bs ε
  have hBs:0≤Bs:=sourceCap_nonneg Mcap Bmask L hMcap.le hmask _
  have hκ0:0≤κ:=by linarith
  have hb:0≤b:=zero_le_one.trans hhi
  have hr:0<r:=(bounds Mcap Bs κ ε hMcap.le hBs hκ0 hε).2.2.2.1
  have hr1:r/4≤1:=by
    have hh:=bounds Mcap Bs κ ε hMcap.le hBs hκ0 hε
    have hrs:r≤amplification ε/100:=min_le_left _ _
    linarith [hh.2.1]
  have hMp:0≤Mp:=bandWidth_nonneg Mcap Bs ε hMcap.le hBs hε _
  have hMc:0<Mc:=band_positive Mcap Bs ε hMcap hBs hε k
  have hMpM:Mp≤Mcap:=bandWidth_le _ _ _ _
  have hMcM:Mc≤Mcap:=bandWidth_le _ _ _ _
  have hac:0<ac:=lowerAt_pos a b Mcap ε ha _
  have haca:ac≤a:=CenteredMomentEnergyProfiles.lower_antitone a b ha (Nat.zero_le _)
  have haclo:ac≤1/4:=haca.trans hlo
  have hLc:0≤Lc:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hLp:0≤Lp:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hreq:=request_bounds Mcap Bmask Lc hMcap.le hmask hLc
  have hreqFinal:Lreq≤range Mcap Bmask L (count Mcap ε):=
    request_le_final Mcap Bmask L ε hMcap.le hmask k hk
  have hRange:=range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)
  have hA:0≤A:=by dsimp [A];positivity
  have hMA:Mp≤A:=by dsimp [A];linarith [range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)]
  have hready:readyBudget A Bmask≤Bs:=
    readyBudget_le_schedule Mcap Bmask L ε A Bmask hMcap.le hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤Mc:=parent_drop Mcap Bs ε hε k
  have hmesh:0≤fineMesh Mcap Bmask L κ ε:=
    (fineMesh_pos Mcap Bmask L κ ε hMcap.le hmask hκ0 hε).le
  have hsupport:lowerAt a b Mcap ε k=ac/max 1 b:=child_support a b Mcap ε k hk
  have hrequest:2*max Lreq Mp+r/4≤Lp:=previous_admits Mcap Bmask L ε Mp (r/4)
    hMcap.le hmask hMpM hr1 k hk
  have hhighL:max Lc Mp≤Lp:=by
    have hh:max Lc Mp≤Lreq:=max_le hreq.2.1 (hMpM.trans hreq.2.2)
    have hg:0≤max Lreq Mp:=hreq.1.trans (le_max_left _ _)
    have hx:=le_max_left Lreq Mp
    linarith
  have href:Mp+Bmask+Mc/100≤Lreq:=by
    have hh:=actual_contours Mcap Bmask Lc Mp Mc 0 hMcap.le hmask hMpM hMcM (by norm_num)
    exact (le_max_right _ _).trans hh
  obtain ⟨Jold,Sold,hprev⟩:=hold
  obtain ⟨Slow,Jlow,hlow⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCappedLowStage.actual_capped_low (α:=α) M H hH
    W aslot bslot a b radial Bmask L lo hi Mcap κ ε hW haslot hWs hbslot ha hb hrad
    hmask hMcap.le hκ hε  hκone k hk ⟨Jold,Sold,hprev⟩
  obtain ⟨Uhigh,Jhigh,hhigh⟩:=ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyNaturalHighStage.actual_high_stage (α:=α) M H hH
    W hW aslot bslot lo hi ac b radial haslot hWs hbslot hac haclo hhi (by linarith)
    Mcap A Bs Bmask Mp Mc Lc (fineMesh Mcap Bmask L κ ε) Mc κ ε k hMc hMcap.le hA hBs hmask
    hMp hMc.le hLc hmesh hMA hready hκ  hκone hε le_rfl hdrop Jold Sold Jlow Slow
  obtain ⟨d,Lgrow,Llow,hd,hd1,hLg,hgoal,hLexact,hLlow,hLupper,hzeroStage⟩:=
    ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyNaturalZeroStage.actual_zero_stage (α:=α) M H hH
      W aslot bslot (fineMesh Mcap Bmask L κ ε) lo hi κ ac b radial Bmask Lc Mp Mc Mcap Bs ε Mc k
      haslot hWs hW hmesh hκ  hκone hac haclo hhi hrad hmask hLc hMp hMc.le hMcap.le hBs
      hε hMc le_rfl hdrop
  have hLlowReq:Llow≤Lreq:=by
    rw [hLlow,hLexact]
    exact actual_contours Mcap Bmask Lc Mp Mc d hMcap.le hmask hMpM hMcM hd1
  have hLgrowLow:Lgrow≤Llow:=by rw [hLlow];exact le_max_left _ _
  have hLgrowReq:Lgrow≤Lreq:=hLgrowLow.trans hLlowReq
  have hzeroCap:max Mp (2*Lgrow)≤Lp:=by
    have hm:Mp≤Lreq:=hMpM.trans hreq.2.2
    have hh:=le_max_left Lreq Mp
    apply max_le <;> linarith
  have hzeroReady:readyBudget (max Mp (2*Lgrow)) Bmask≤Bs:=by
    have hc:max Mp (2*Lgrow)≤A:=by
      apply max_le
      · exact hMA
      · dsimp [A];linarith
    apply le_trans _ hready
    unfold readyBudget
    linarith
  obtain ⟨Jzero,Uzero,hzero⟩:=hzeroStage Lp hLp hzeroCap hzeroReady Jold Jlow Sold Slow
  have hmarg:=margins Mcap Bs κ ε hMcap.le hBs hκ0 hε k
  apply OAI.SevenEighths.CenteredMomentEnergyCappedSuccessorPacking.certified_from_stages (α:=α) M H hH
    W bslot a b radial Bmask L lo hi Mcap κ ε ha hmask hMcap.le hκ0 hε k
    (stageLoss Mcap Bs ε (k+1)) (physicalLoss Mcap Bs ε k) (reflectedLoss Mcap Bs ε k)
    le_rfl (hmarg.2.2.2.1.trans hmarg.2.2.2.2) hmarg.2.2.2.2 ⟨Jold,Sold,hprev⟩
  · refine ⟨Jzero,Uzero,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Cz,hCz,hzeroZ⟩:=hzero η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Cz*(Clow+C₀+C₁+1),by positivity,?_⟩
    filter_upwards [hprevZ,hlowZ,hzeroZ] with Z hp hl hz
    have hzz : ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        Lp Mc (stageLoss Mcap Bs ε k) Z Jold Sold C₀ := hp.2.1
    have hpp : PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
        Lp (fineMesh Mcap Bmask L κ ε) lo hi Mc (stageLoss Mcap Bs ε k)
        κ Z η₀ Q Jold Sold C₁ := hp.2.2
    rw [hsupport] at hzz hpp
    have hlowRestricted:=zeroLowAt_transport (internalQ Q η₀)
      ac b radial Bmask Lreq Mp (physicalLoss Mcap Bs ε k) Z
      ac b radial Bmask Llow Mp (physicalLoss Mcap Bs ε k) Jlow Jlow Slow Slow Clow Clow
      hp.1.le le_rfl le_rfl le_rfl le_rfl hLlowReq le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.2
    exact hz.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzz hpp hlowRestricted
  · refine ⟨Jlow,Slow,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Clow,hClow,?_⟩
    filter_upwards [hlowZ] with Z hl
    exact positiveLowAt_transport (α:=α) M H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
      ac b radial Bmask Lc Mp (physicalLoss Mcap Bs ε k) η₀ Q Jlow Jlow Slow Slow Clow Clow
      hl.1.le le_rfl le_rfl le_rfl le_rfl hreq.2.1 le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
  · refine ⟨Jhigh,Uhigh,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Ch,hCh,hhighZ⟩:=hhigh η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Ch*(C₀+C₁+Clow+1),by positivity,?_⟩
    filter_upwards [hprevZ,hlowZ,hhighZ] with Z hp hl hh
    have hzz : ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε k) b radial Bmask
        Lp Mc (stageLoss Mcap Bs ε k) Z Jold Sold C₀ := hp.2.1
    have hpp : PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε k) b radial Bmask
        Lp (fineMesh Mcap Bmask L κ ε) lo hi Mc (stageLoss Mcap Bs ε k)
        κ Z η₀ Q Jold Sold C₁ := hp.2.2
    rw [hsupport] at hzz hpp
    have hzSmall:=zeroAt_transport (internalQ Q η₀)
      (ac/max 1 b) b radial Bmask Lp Mc (stageLoss Mcap Bs ε k) Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k)
      Jold Jold Sold Sold C₀ C₀ hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC₀.le le_rfl hzz
    have hpSmall:=positiveAt_transport (α:=α) M H hH W bslot
      (ac/max 1 b) b radial Bmask Lp (fineMesh Mcap Bmask L κ ε) lo hi Mc (stageLoss Mcap Bs ε k) κ Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k) η₀ Q
      Jold Jold Sold Sold C₁ C₁ hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC₁.le le_rfl hpp
    have hlRestricted:=positiveLowAt_transport (α:=α) M H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
      ac b radial Bmask (Mp+Bmask+Mc/100) Mp (physicalLoss Mcap Bs ε k) η₀ Q
      Jlow Jlow Slow Slow Clow Clow hp.1.le le_rfl le_rfl le_rfl le_rfl href le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
    exact hh.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzSmall hpSmall hlRestricted

end SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessor

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core


/- From OAI.NumberTheory.DirichletL.Energy.CertifiedExistence. -/
namespace ZetaZeroFree.Analytic.Moments.Unconditional.Core

open OAI OAI.SevenEighths

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCertifiedExistence

open OAI.SevenEighths.CenteredMomentEnergyCertifiedExistence hiding certified_bands terminal_certificate

open HeckeFamily ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCappedWidthInduction

open OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction hiding certified_floor

open ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessor OAI.SevenEighths.CenteredMomentEnergyCappedRadialTransport

open OAI.SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessor hiding actual_successor

open OAI.SevenEighths.CenteredMomentEnergyCappedRadialTransport

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

open OAI.SevenEighths.CenteredMomentEnergyWidthSchedule

local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

variable (M:Ideal O)[NeZero M]

local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem certified_bands (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(haUpper:a≤1/4)(hb:1≤b)(hrad:2≤radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    (hκ:1 ≤ κ):
    ∀k:ℕ,k≤count Mcap ε→
      OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k:=by
  intro k
  induction k with
  | zero =>
    intro _
    exact certified_floor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le (by linarith) hε  hκ
  | succ k ih =>
    intro hk
    have hprevious:=ih (Nat.le_of_succ_le hk)
    have hstep:k<count Mcap ε:=by omega
    exact actual_successor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε  hκ
      k hstep hprevious

theorem terminal_certificate (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0<aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤bslot)(ha:0<a)(haUpper:a≤1/4)(hb:1≤b)(_hrad:0<radial)
    (hmask:0≤Bmask)(hMcap:0<Mcap)(hκ0:(3/4:ℝ)≤κ)(hε:0<ε)
    (hκ:1 ≤ κ):
    OAI.SevenEighths.CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε):=by
  apply certified_from_max_two (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε
  exact certified_bands (α:=α) M H hH W aslot bslot a b (max 2 radial) Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb (le_max_left _ _) hmask hMcap hκ0 hε  hκ _ le_rfl

end SevenEighths.CenteredMomentEnergyCertifiedExistence

end

end ZetaZeroFree.Analytic.Moments.Unconditional.Core

namespace ZetaZeroFree.Analytic.Moments.Unconditional
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ZetaZeroFree.Analytic.Moments
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonProfile CenteredMomentEnergyState CenteredMomentNaturalRowSource
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem nonfixed_zero_at (a b radial B L Mcap ε : ℝ)
    (ha : 0 < a) (haUpper : a ≤ 1 / 4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hB : 0 ≤ B) (hM : 0 < Mcap) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ZeroAt (internalQ Q η₀) a b radial B L Mcap ε Z J S C := by
  have hcert := ZetaZeroFree.Analytic.Moments.Unconditional.Core.SevenEighths.CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := Fin 0) M ⊤ le_top (fun _ : ℝ => (0 : ℂ)) 1 1 a b radial B L 0 0 Mcap 1 ε
    (by norm_num) (by simp) contDiff_const (by norm_num) ha haUpper hb hrad hB hM
    (by norm_num) hε  le_rfl
  obtain ⟨J, S, he⟩ := CenteredMomentEnergyCappedWidthInduction.certified_terminal
    (α := Fin 0) M ⊤ le_top (fun _ : ℝ => (0 : ℂ)) 1 a b radial B L 0 0 Mcap 1 ε
    hB hM.le (by norm_num) hε hcert
  refine ⟨J, S, ?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C, Cpositive, hC, _, hz⟩ := he η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C, hC, ?_⟩
  filter_upwards [hz] with Z hZ
  exact ⟨hZ.1, hZ.2.1⟩

theorem nonfixed_mixed_at (a b radial B L Mcap ε : ℝ)
    (ha : 0 < a) (haUpper : a ≤ 1 / 4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hB : 0 ≤ B) (hM : 0 < Mcap) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        NonfixedMixedAt (internalQ Q η₀) a b radial B L Mcap ε Z J S C := by
  obtain ⟨J₀, S₀, hz⟩ := nonfixed_zero_at M a b radial B L Mcap ε
    ha haUpper hb hrad hB hM hε
  obtain ⟨J, S, Cheight, hCheight, he⟩ := zero_at_independent_heights a b ha S₀
  refine ⟨J, S, ?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C, hC, hz⟩ := hz η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C * Cheight, mul_pos hC hCheight, ?_⟩
  filter_upwards [hz] with Z hZ
  exact ⟨hZ.1, he _ radial B L Mcap ε Z C J₀
    (zero_le_one.trans hZ.1.le) hC.le hZ.2⟩


theorem all_natural_mixed_at (a b radial B Bfixed L Mcap ε : ℝ)
    (ha : 0 < a) (haUpper : a ≤ 1 / 4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hB : 0 ≤ B) (hBfixed : 0 ≤ Bfixed) (hM : 0 < Mcap) (hε : 0 < ε) :
    ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
        ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ AllNaturalMixedAt a b radial B Bfixed L Mcap ε Z J S C := by
  obtain ⟨Jn, Sn, hn⟩ := nonfixed_mixed_at M a b radial B L Mcap ε
    ha haUpper hb hrad hB hM hε
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cn, hCn, hz⟩ := hn η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨J, S, C, hC, he⟩ := all_natural_mixed_uniform_join a b radial B Bfixed L Mcap ε
    ha (by linarith) hBfixed hε (internalQ Q η₀) hQ0 Jn Sn Cn hCn.le
  refine ⟨J, S, C, hC, ?_⟩
  filter_upwards [hz] with Z hZ
  exact ⟨hZ.1, he Z hZ.2⟩

theorem all_nonprincipal_at (a b radial B L Mcap ε : ℝ)
    (ha : 0 < a) (haUpper : a ≤ 1 / 4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hB : 0 ≤ B) (hM : 0 < Mcap) (hε : 0 < ε) :
    ∀ η₀ : Character, ∀ Q : Ideal O, Q ≤ M →
      internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ J : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
        ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ AllNonprincipalAt a b radial B L Mcap ε Z J S C := by
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨J, S, C, hC, hz⟩ := all_natural_mixed_at M a b radial B
    (Mcap + B + 1) L Mcap ε ha haUpper hb hrad hB (by linarith) hM hε
    η₀ Q hQM hQ0 hQt hQ72
  refine ⟨J, S, C, hC, ?_⟩
  filter_upwards [hz, eventually_ge_atTop ((fixedConductorFactor : ℝ) * radial)] with Z hZ hcap
  refine ⟨hZ.1, ?_⟩
  intro s hw hpuncture W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  have hbudget := live_masked_modulus_budget Z B radial Mcap s hw hrad.le hcap
  have he := hZ.2 s.restrictLive hw hpuncture hbudget W₁ W₂ hs₁ hs₂ X₁ X₂ t₁ t₂ hX₁ hX₂ hLX₁ hLX₂
  rw [s.energy_restrictLive] at he
  exact he


end
end ZetaZeroFree.Analytic.Moments.Unconditional
