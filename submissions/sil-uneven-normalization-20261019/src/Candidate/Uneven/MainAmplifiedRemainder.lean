import Candidate.Uneven.MainParameters
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule
import Candidate.Uneven.MainZeroPayment
import Candidate.Uneven.MainErrorMain
import Candidate.Uneven.MainCellGeometry
import Candidate.Cycle63.Physical.SecondZero.Source
import Candidate.Cycle63.Physical.InitialMass.GeometryErrorRemainder
import Candidate.Cycle63.Arithmetic.LocalReserves
import Candidate.Cycle63.Physical.FinalError.Payment

/- Original module: Candidate.Uneven.MainErrorLoss. -/
section
/- Copyright (c) 2026 Sil. Apache-2.0. Prepared with OpenAI Codex assistance. -/

set_option autoImplicit false
namespace OAI.SevenEighths.MainReconstruction
noncomputable section
open Cycle63InitialMass

/-- The smaller error reserve is paid using the actual capped loss unit. -/
theorem main_paid_error_loss (Mmin εaffine M reserve loss : ℝ)
    (hMmin : 0< Mmin) (hM : Mmin≤ M)
    (hεcap : εaffine≤ Mmin/1000000000)
    (hr : Sil.Uneven.MainSource.errorReserve≤ reserve)
    (hloss : loss≤64*geometryLossUnit Mmin εaffine) :
    -M*reserve+loss≤-M*(1/2000000000) := by
  have hu : geometryLossUnit Mmin εaffine≤εaffine/128 := min_le_left _ _
  have hres := mul_le_mul_of_nonneg_left hr (hMmin.trans_le hM).le
  norm_num [Sil.Uneven.MainSource.errorReserve] at hres
  linarith only [hu,hres,hεcap,hloss,hM,hMmin]

end
end OAI.SevenEighths.MainReconstruction
end

/- Original module: Candidate.Uneven.MainAmplifiedRemainder. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.MainReconstruction
open OAI.SevenEighths.Cycle63InitialMass

noncomputable section
open Sil.Uneven.MainSource
open scoped BigOperators
open HeckeFamily CanonicalQuadraticSieve CenteredMomentPrimeElements
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstAmplificationChoice
open Cycle63SecondZero
local notation "O" => HeckeFamily.O
variable {plane : Plane}

/-- The actual prime average costs only the three extracted branches.
The prime pool is not replaced by a polynomial counting estimate. -/
theorem actual_error_zero_prime_average (P : Finset (Ideal O)) (Z ε : ℝ)
    (hne : P.Nonempty) (hZ : 1< Z) (hε : 0 ≤ ε)
    (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes) :
    (56/(P.card:ℝ))*errorZeroPrimeWeight Z ε P ≤ 168 := by
  have hn : (0:ℝ)< P.card := by exact_mod_cast hne.card_pos
  have hpoint (q : elementPool P) (i : Fin 3) :
      Z^(-ε*errorRemoval q.val Z (errorIndex i+1)) ≤ 1 := by
    have hdata := elementPool_data P hp hbad q.val q.property
    have hQ : Ideal.span {q.val}≠0 := hdata.2.2.2.1.1
    have hw : 0 ≤ errorRemoval q.val Z (errorIndex i+1) := by
      unfold errorRemoval
      exact mul_nonneg (Nat.cast_nonneg _) (ideal_log_nonneg _ hQ Z hZ)
    simpa only [neg_mul] using
      (Real.rpow_le_rpow_of_exponent_le hZ.le (neg_nonpos.mpr (mul_nonneg hε hw))).trans_eq
        (Real.rpow_zero Z)
  have hw : errorZeroPrimeWeight Z ε P ≤ 3*(P.card:ℝ) := by
    calc
      _ ≤ ∑q : elementPool P,∑i : Fin 3,(1:ℝ) :=
        Finset.sum_le_sum (fun q _=> Finset.sum_le_sum (fun i _=> hpoint q i))
      _=3*(P.card:ℝ) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
          Fintype.card_coe,elementPool_card P hp hbad]
        ring
  calc
    _ ≤ (56/(P.card:ℝ))*(3*(P.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _=168 := by field_simp; norm_num

/-- A strict zero-frequency saving remains even after cancelling the
entire error prime pool. The small analytic losses are explicit. -/
theorem geometry_zero_exponent_saving (Z M A a ξ reserve padding ε εmass B count β : ℝ)
    (hM : 0 ≤ M) (hb : widthLo ≤ β ∧ β ≤ widthHi)
    (ha : a ≤ M*Sil.Uneven.MainSource.amp plane β)
    (hloss : frequencyLoss Z 32 ξ+reserve+ε*(A+padding)+B*εmass+3*count ≤ M/380) :
    zeroPaymentExponent Z M A a ξ reserve padding ε εmass B+3*count ≤ -M/20 := by
  have hamp := mul_le_mul_of_nonneg_left (Sil.Uneven.MainSource.scheduling_guards plane hb).2.2.2.1.le hM
  unfold zeroPaymentExponent
  linarith


/-- The three extracted branches retain a uniform strict saving after the
full prime average and arithmetic-label sums. The factor 1872 is the exact
sum of their existing multiplicities, rather than a new label count. -/
theorem geometry_error_branches_saving (Z Mmin εaffine M loss : ℝ)
    (hZ : 1 ≤ Z) (hMmin : 0< Mmin) (hM : Mmin ≤ M)
    (hεcap : εaffine≤ Mmin/1000000000)
    (hloss : loss ≤ 64*geometryLossUnit Mmin εaffine) :
    Z^loss*(∑i : Fin 3,16*(errorIndex i+2:ℝ)^2*
      Z^(-M*MainError.branchReserve (errorIndex i+1))) ≤ 
      1872*Z^(-M*(1/2000000000:ℝ)) := by
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hres (k : ℕ) : Sil.Uneven.MainSource.errorReserve ≤ MainError.branchReserve k := by
    norm_num [MainError.branchReserve,errorReserve]
  have hpoint (i : Fin 3) :
      Z^loss*(16*(errorIndex i+2:ℝ)^2*
        Z^(-M*MainError.branchReserve (errorIndex i+1))) ≤ 
      (16*(errorIndex i+2:ℝ)^2)*Z^(-M*(1/2000000000:ℝ)) := by
    have he := main_paid_error_loss Mmin εaffine M
      (MainError.branchReserve (errorIndex i+1)) loss hMmin hM hεcap (hres _) hloss
    calc
      _ = (16*(errorIndex i+2:ℝ)^2)*
          Z^(-M*MainError.branchReserve (errorIndex i+1)+loss) := by
        rw [Real.rpow_add hz]; ring
      _  ≤  _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ he) (by positivity)
  calc
    _ = ∑i : Fin 3,Z^loss*(16*(errorIndex i+2:ℝ)^2*
        Z^(-M*MainError.branchReserve (errorIndex i+1))) := Finset.mul_sum ..
    _  ≤  ∑i : Fin 3,(16*(errorIndex i+2:ℝ)^2)*Z^(-M*(1/2000000000:ℝ)) :=
      Finset.sum_le_sum (fun i _=> hpoint i)
    _ = _ := by rw [←Finset.sum_mul]; norm_num [Fin.sum_univ_succ,errorIndex]


/-- Width-one amplification pays the main-source amplifier power exactly.
The coefficient is uniform across the 600000001 admissible cells. -/
theorem geometry_main_prime_payment (P : Finset (Ideal O)) (Z β loss Ccap E : ℝ)
    (hZ : 0< Z) (hb : widthLo ≤ β ∧ β ≤ widthHi)
    (hC : 0 ≤ Ccap) (hE : 0 ≤ E)
    (hpool : Z^(Sil.Uneven.MainSource.amp plane β-loss) ≤ (P.card:ℝ)) :
    (56/(P.card:ℝ))*((Ccap+6*Sil.Uneven.MainSource.amp plane β)/(Sil.Uneven.MainSource.amp plane β/2))*
      (E*Z^(Sil.Uneven.MainSource.amp plane β)) ≤ 11200000*(Ccap+1)*E*Z^loss := by
  have ha := Sil.Uneven.MainSource.scheduling_guards plane hb
  have hap := Sil.Uneven.MainSource.amplifier_pos plane hb
  have hp : (0:ℝ)< P.card := (Real.rpow_pos_of_pos hZ _).trans_le hpool
  have hfac : (Ccap+6*Sil.Uneven.MainSource.amp plane β)/(Sil.Uneven.MainSource.amp plane β/2) ≤ 
      200000*(Ccap+1) := by
    apply (div_le_iff₀ (half_pos hap)).mpr
    have hmul := mul_le_mul_of_nonneg_left ha.2.2.1 hC
    norm_num [Sil.Uneven.MainSource.amplifierMinimum] at hmul
    nlinarith
  have hratio : Z^(Sil.Uneven.MainSource.amp plane β)/(P.card:ℝ) ≤ Z^loss := by
    apply (div_le_iff₀ hp).mpr
    calc
      _=Z^(Sil.Uneven.MainSource.amp plane β-loss)*Z^loss := by
        rw [←Real.rpow_add hZ]; congr 1; ring
      _ ≤ Z^loss*(P.card:ℝ) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hpool
          (Real.rpow_nonneg hZ.le loss)
  calc
    _=56*((Ccap+6*Sil.Uneven.MainSource.amp plane β)/(Sil.Uneven.MainSource.amp plane β/2))*E*
        (Z^(Sil.Uneven.MainSource.amp plane β)/(P.card:ℝ)) := by ring
    _ ≤ 56*(200000*(Ccap+1))*E*Z^loss := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (by norm_num)) hE
      · exact hratio
      · positivity
      · positivity
    _=_ := by ring

end
end OAI.SevenEighths.MainReconstruction
end
