import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorRemainder
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.LocalReserves
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalError.Payment
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentPrimeElements
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplificationChoice
open Cycle63SecondZero

/-- The actual prime average costs only the three extracted branches.
The prime pool is not replaced by a polynomial counting estimate. -/
theorem actual_error_zero_prime_average (P : Finset (Ideal O)) (Z ε : ℝ)
    (hne : P.Nonempty) (hZ : 1<Z) (hε : 0≤ε)
    (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes) :
    (56/(P.card:ℝ))*errorZeroPrimeWeight Z ε P≤168 := by
  have hn : (0:ℝ)<P.card := by exact_mod_cast hne.card_pos
  have hpoint (q : elementPool P) (i : Fin 3) :
      Z^(-ε*errorRemoval q.val Z (errorIndex i+1))≤1 := by
    have hdata := elementPool_data P hp hbad q.val q.property
    have hQ : Ideal.span {q.val}≠0 := hdata.2.2.2.1.1
    have hw : 0≤errorRemoval q.val Z (errorIndex i+1) := by
      unfold errorRemoval
      exact mul_nonneg (Nat.cast_nonneg _) (ideal_log_nonneg _ hQ Z hZ)
    simpa only [neg_mul] using
      (Real.rpow_le_rpow_of_exponent_le hZ.le (neg_nonpos.mpr (mul_nonneg hε hw))).trans_eq
        (Real.rpow_zero Z)
  have hw : errorZeroPrimeWeight Z ε P≤3*(P.card:ℝ) := by
    calc
      _≤∑q : elementPool P,∑i : Fin 3,(1:ℝ) :=
        Finset.sum_le_sum (fun q _=>Finset.sum_le_sum (fun i _=>hpoint q i))
      _=3*(P.card:ℝ) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
          Fintype.card_coe,elementPool_card P hp hbad]
        ring
  calc
    _≤(56/(P.card:ℝ))*(3*(P.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _=168 := by field_simp; norm_num

variable [Cycle63.AffineLedger] in
/-- A strict zero-frequency saving remains even after cancelling the
entire error prime pool. The small analytic losses are explicit. -/
theorem geometry_zero_exponent_saving (Z unit Mrow A a ξ reserve padding ε εmass B count β : ℝ)
    (hunit : 0≤unit) (hb : Cycle63.AffineLedger.firstCellTop≤β ∧ β≤Cycle63.AffineLedger.slotTop)
    (ha : a≤unit*Cycle63.AffineLedger.amp β)
    (hloss : frequencyLoss Z 32 ξ+reserve+ε*(A+padding)+B*εmass+3*count≤unit/380) :
    zeroPaymentExponent Z unit Mrow A a ξ reserve padding ε εmass B+3*count≤
      -unit*Cycle63.AffineLedger.zeroSaving+(unit-Mrow) := by
  have hamp := mul_le_mul_of_nonneg_left (Cycle63.AffineLedger.amp_bounds hb).2 hunit
  have hzero : Cycle63.AffineLedger.amplifierCap+1/380+Cycle63.AffineLedger.zeroSaving ≤
      Cycle63.AffineLedger.zeroReserve :=
    Cycle63.AffineLedger.zeroReserve_ge
  have hz := mul_le_mul_of_nonneg_left hzero hunit
  unfold zeroPaymentExponent
  linarith

variable [Cycle63.AffineLedger] in
/-- The three extracted branches retain a uniform strict saving after the
full prime average and arithmetic-label sums. The factor 1872 is the exact
sum of their existing multiplicities, rather than a new label count. -/
theorem geometry_error_branches_saving (Z Mmin εaffine M loss : ℝ)
    (hZ : 1≤Z) (hMmin : 0<Mmin) (hM : Mmin≤M)
    (hloss : loss≤64*geometryLossUnit Mmin εaffine) :
    Z^loss*(∑i : Fin 3,16*(errorIndex i+2:ℝ)^2*
      Z^(-M*Cycle63FinalError.branchReserve (errorIndex i+1)))≤
      1872*Z^(-M*((Cycle63.AffineLedger.lowReserve/2):ℝ)) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hres (k : ℕ) : (Cycle63.AffineLedger.lowReserve:ℝ)≤Cycle63FinalError.branchReserve k := by
    have hr := Cycle63.AffineLedger.lowReserve_le_errorReserves
    unfold Cycle63FinalError.branchReserve
    split_ifs
    · exact hr.1
    · exact hr.2.1
    · exact hr.2.2
  have hpoint (i : Fin 3) :
      Z^loss*(16*(errorIndex i+2:ℝ)^2*
        Z^(-M*Cycle63FinalError.branchReserve (errorIndex i+1)))≤
      (16*(errorIndex i+2:ℝ)^2)*Z^(-M*((Cycle63.AffineLedger.lowReserve/2):ℝ)) := by
    have he := geometry_paid_loss Mmin εaffine M
      (Cycle63FinalError.branchReserve (errorIndex i+1)) loss hMmin hM (hres _) hloss
    calc
      _ = (16*(errorIndex i+2:ℝ)^2)*
          Z^(-M*Cycle63FinalError.branchReserve (errorIndex i+1)+loss) := by
        rw [Real.rpow_add hz]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ he) (by positivity)
  calc
    _ = ∑i : Fin 3,Z^loss*(16*(errorIndex i+2:ℝ)^2*
        Z^(-M*Cycle63FinalError.branchReserve (errorIndex i+1))) := Finset.mul_sum ..
    _ ≤ ∑i : Fin 3,(16*(errorIndex i+2:ℝ)^2)*Z^(-M*((Cycle63.AffineLedger.lowReserve/2):ℝ)) :=
      Finset.sum_le_sum (fun i _=>hpoint i)
    _ = _ := by rw [←Finset.sum_mul]; norm_num [Fin.sum_univ_succ,errorIndex]

variable [Cycle63.AffineLedger] in
/-- Width-one amplification pays the main-source amplifier power exactly.
The coefficient is uniform across the admissible cells. -/
theorem geometry_main_prime_payment (P : Finset (Ideal O)) (Z β loss Ccap E : ℝ)
    (hZ : 0<Z) (hb : Cycle63.AffineLedger.firstCellTop≤β ∧ β≤Cycle63.AffineLedger.slotTop)
    (hC : 0≤Ccap) (hE : 0≤E)
    (hpool : Z^(Cycle63.AffineLedger.amp β-loss)≤(P.card:ℝ)) :
    (56/(P.card:ℝ))*((Ccap+6*Cycle63.AffineLedger.amp β)/(Cycle63.AffineLedger.amp β/2))*
      (E*Z^(Cycle63.AffineLedger.amp β))≤Cycle63.AffineLedger.primePaymentConstant*(Ccap+1)*E*Z^loss := by
  have ha := Cycle63.AffineLedger.amp_bounds hb
  have hap := Cycle63.AffineLedger.amp_pos hb
  have hp : (0:ℝ)<P.card := (Real.rpow_pos_of_pos hZ _).trans_le hpool
  have hK := Cycle63.AffineLedger.primePaymentConstant_ge
  have hK0 : 0 < Cycle63.AffineLedger.primePaymentConstant :=
    Cycle63.AffineLedger.primePaymentConstant_pos
  have hfloor := Cycle63.AffineLedger.amplifierFloor_pos
  have hfac : (Ccap+6*Cycle63.AffineLedger.amp β)/(Cycle63.AffineLedger.amp β/2)≤
      Cycle63.AffineLedger.primePaymentConstant/56*(Ccap+1) := by
    apply (div_le_iff₀ (half_pos hap)).mpr
    have h1 : 2/Cycle63.AffineLedger.amp β ≤ 2/Cycle63.AffineLedger.amplifierFloor :=
      div_le_div_of_nonneg_left (by norm_num) hfloor ha.1
    have hKa : (2/Cycle63.AffineLedger.amp β+12)*Cycle63.AffineLedger.amp β ≤
        Cycle63.AffineLedger.primePaymentConstant/56*Cycle63.AffineLedger.amp β :=
      mul_le_mul_of_nonneg_right (by linarith) hap.le
    have h3 : (2/Cycle63.AffineLedger.amp β+12)*Cycle63.AffineLedger.amp β = 2+12*Cycle63.AffineLedger.amp β := by
      field_simp
    nlinarith [mul_nonneg hC hap.le]
  have hratio : Z^(Cycle63.AffineLedger.amp β)/(P.card:ℝ)≤Z^loss := by
    apply (div_le_iff₀ hp).mpr
    calc
      _=Z^(Cycle63.AffineLedger.amp β-loss)*Z^loss := by
        rw [←Real.rpow_add hZ]; congr 1; ring
      _≤Z^loss*(P.card:ℝ) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hpool
          (Real.rpow_nonneg hZ.le loss)
  calc
    _=56*((Ccap+6*Cycle63.AffineLedger.amp β)/(Cycle63.AffineLedger.amp β/2))*E*
        (Z^(Cycle63.AffineLedger.amp β)/(P.card:ℝ)) := by ring
    _≤56*(Cycle63.AffineLedger.primePaymentConstant/56*(Ccap+1))*E*Z^loss := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (by norm_num)) hE
      · exact hratio
      · positivity
      · positivity
    _=_ := by ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
