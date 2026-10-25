/- Copyright (c) 2026 Sil. Apache-2.0.
Pay every component of the actual finite-supplier budget at the first
common reference. Profiles and independent height remain explicit and
homogeneous; no moving constant is introduced.
-/
import Candidate.SilPrior.FourthPower.RepairedFirstScalarBudget
import Candidate.SilPrior.FourthPower.MixedFirstAllocatedRemainders

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedPaidFirstBudget
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceProfileMass
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open EisensteinSchwartzPoisson
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedOriginalTail MixedFirstExceptionalNormalization MixedFirstAllocatedRemainders
open RepairedRootParameters RepairedRawContext RepairedFirstPoint RepairedCapEvent
open RepairedRawReference RepairedSupplierProfiles RepairedLargeSupplierBudget RepairedFirstScalarBudget
open MixedInnerExceptionalBlock
open MixedPrincipalCentered
open MixedFirstProfileEnvelope (height)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ}
variable {η η₀ : Character} (d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀)

-- Keep the checked Point constructor's concrete classical index instance.
local instance (priority := 2000) (p : Point d) : DecidableEq p.Index := Classical.decEq _

def firstLoss : ℝ := windowLoss ε+2*cutoffLoss N ε
def slotShapeCap : ℝ := Kslot^(2*N)*((2:ℝ)^N)^(4/3:ℝ)
def rootZero (c : Constants) : ℝ :=
  c.zero*selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*(profileCap d.root)^2*
    (2:ℝ)^(2*N)*(9/4:ℝ)^2*Kslot^(2*N)
def rootNonexceptional (U : Controls) (c : Constants) (tp : ℝ) : ℝ :=
  c.nonexceptional*(Kslot^(4*N)*(2:ℝ)^N/(1/4:ℝ)^2)*
    profileCore d.root Kslot N U.nonexceptionalDegree U.nonexceptionalControl d.t₀ tp d.V*Kslot^(2*N)
def rootExceptional (U : Controls) (c : Constants) (tp : ℝ) : ℝ :=
  c.exceptional*selectedCap N Kslot*heightBase tp^(2*U.exceptionalDegree)*
    (profileEnvelope d.root N Kslot U.exceptionalDegree U.exceptionalControl 1 0)^2*
    slotShapeCap (N:=N) (Kslot:=Kslot)*(2/9:ℝ)^(-2/3:ℝ)
def rootTail (c : Constants) : ℝ := c.tail*selectedCap N Kslot*(profileCap d.root)^2*Kslot^(2*N)
def rootBudget (U : Controls) (c : Constants) (tp : ℝ) : ℝ :=
  256*(rootZero d c+rootNonexceptional d U c tp+rootExceptional d U c tp+rootTail d c)

theorem root_components_nonneg (U : Controls) (c : Constants) (tp : ℝ) (hKslot : 1 ≤ Kslot) :
    0 ≤ rootZero d c ∧ 0 ≤ rootNonexceptional d U c tp ∧
      0 ≤ rootExceptional d U c tp ∧ 0 ≤ rootTail d c := by
  have hcz := c.zero_pos
  have hcn := c.nonexceptional_pos
  have hce := c.exceptional_pos
  have hct := c.tail_pos
  have hc := profileCore_nonneg d.root Kslot N U.nonexceptionalDegree U.nonexceptionalControl
    d.t₀ tp d.V (zero_le_one.trans hKslot) d.hV
  have ht := heightBase_pos tp
  unfold rootZero rootNonexceptional rootExceptional rootTail selectedCap slotShapeCap
  refine ⟨?_,?_,?_,?_⟩ <;> positivity

theorem rootBudget_nonneg (U : Controls) (c : Constants) (tp : ℝ) (hKslot : 1 ≤ Kslot) :
    0 ≤ rootBudget d U c tp := by
  have h := root_components_nonneg d U c tp hKslot
  unfold rootBudget
  exact mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg (add_nonneg h.1 h.2.1) h.2.2.1) h.2.2.2)

theorem first_profile_cap (p : Point d) : profileCap p.source ≤ profileCap d.root := by
  exact live_profile_cap_le (allocationSource d.root (by norm_num) d.cover p.label.val.1 p.allocation)

theorem first_profile_core (p : Point d) (U : Controls) (tp : ℝ) :
    profileCore p.source Kslot N U.nonexceptionalDegree U.nonexceptionalControl d.t₀ tp d.V =
      profileCore d.root Kslot N U.nonexceptionalDegree U.nonexceptionalControl d.t₀ tp d.V := rfl

theorem first_profile_envelope (p : Point d) (degree : ℕ) (control : Finset (ℕ×ℕ)) :
    profileEnvelope p.source N Kslot degree control Z (cutoffLoss N ε) =
      profileEnvelope d.root N Kslot degree control 1 0*Z^(cutoffLoss N ε) := by
  change profileEnvelope d.root N Kslot degree control Z (cutoffLoss N ε) = _
  unfold profileEnvelope
  simp only [Real.one_rpow,mul_one]
  ring

theorem slot_shape_cap (hcard : Fintype.card ι ≤ N) (hKslot : 1 ≤ Kslot) :
    slotCost d.root ≤ slotShapeCap (N:=N) (Kslot:=Kslot) := by
  have hm := product_slot_cap d.root.M N Kslot hcard hKslot
    (fun i => zero_le_one.trans (d.root.hM i)) d.hM
  have hp : 0 ≤ ∏ i,d.root.M i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (d.root.hM i))
  have hm2 : (∏ i,d.root.M i)^2 ≤ Kslot^(2*N) := by
    apply (pow_le_pow_left₀ hp hm 2).trans_eq
    rw [← pow_mul]
    congr 1
    omega
  have hd : (2:ℝ)^Fintype.card ι ≤ (2:ℝ)^N := pow_le_pow_right₀ (by norm_num) hcard
  unfold slotCost slotShapeCap
  simp only [d.hunit,pairNorm,map_one,Nat.cast_one,one_mul,div_one]
  exact mul_le_mul hm2 (Real.rpow_le_rpow (by positivity) hd (by norm_num))
    (Real.rpow_nonneg (by positivity) _) (by positivity)

theorem paid_coefficients (p : Point d) (U : Controls) (c : Constants) (tp : ℝ)
    (hε : 0 < ε) (hcard : Fintype.card ι ≤ N) (hKslot : 1 ≤ Kslot) (hevent : Event.{u} N ε Z) :
    scalar p*coefficientZero p c ≤ rootZero d c*ref p*Z^(firstLoss (N:=N) (ε:=ε)) ∧
    scalar p*coefficientNonexceptional p U c tp ≤ rootNonexceptional d U c tp*ref p*Z^(firstLoss (N:=N) (ε:=ε)) ∧
    scalar p*coefficientExceptional p U c tp ≤ rootExceptional d U c tp*ref p*Z^(firstLoss (N:=N) (ε:=ε)) ∧
    scalar p*coefficientTail p c ≤ rootTail d c*ref p*Z^(firstLoss (N:=N) (ε:=ε)) := by
  have hz := zero_lt_one.trans d.one_lt_Z
  have hδ := (internal_losses_paid N ε hε).1
  have hw := (cap_spec N ε hε).2.2.1
  have hLoss : 0 ≤ firstLoss (N:=N) (ε:=ε) := by unfold firstLoss; positivity
  have hZloss : 1 ≤ Z^(firstLoss (N:=N) (ε:=ε)) := Real.one_le_rpow d.one_lt_Z.le hLoss
  have hfrozen := frozen_scalar_cap p hcard hKslot
  have hprofile := pow_le_pow_left₀ (profileCap_nonneg p.source) (first_profile_cap d p) 2
  have hroots := root_components_nonneg d U c tp hKslot
  have href := (ref_pos p).le
  have hscalar : 0 ≤ scalar p := sq_nonneg _
  have hzero := zero_geometry_reference p hε hcard hevent
  have hshape := exceptional_shape_reference p hε hevent
  have htail := tail_power_reference p hε hcard hevent
  have hcore := profileCore_nonneg d.root Kslot N U.nonexceptionalDegree U.nonexceptionalControl
    d.t₀ tp d.V (zero_le_one.trans hKslot) d.hV
  have ht := heightBase_pos tp
  have hcz := c.zero_pos
  have hcn := c.nonexceptional_pos
  have hce := c.exceptional_pos
  have hct := c.tail_pos
  have hKslot0 : 0 ≤ Kslot := zero_le_one.trans hKslot
  have hselected : 0 ≤ selectedCap N Kslot := by unfold selectedCap; positivity
  have hbase := referenceBase_nonneg p.tau p.label.val.1 (sourceVolume d.root)
  have hradial : 0 < p.scale := Real.rpow_pos_of_pos hz _
  have hvolume := sourceVolume_pos p.source
  have hprefix := pairNorm_pos p.source.hd.1 p.source.hd.2
  have hmaximum := prefixNormMax_pos p.source.d p.source.hd
  have hminimum := p.source.hL
  have hshape0 : 0 ≤ shape (sourceVolume p.source) (pairNorm p.source.d)
      (prefixNormMax p.source.d) p.source.L p.scale 1 := by
    unfold shape
    positivity
  refine ⟨?_,?_,?_,?_⟩
  · have hp : Z^(2*cutoffLoss N ε) ≤ Z^(firstLoss (N:=N) (ε:=ε)) :=
      Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le (by unfold firstLoss; linarith)
    calc
      _ = (c.zero*selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*(profileCap p.source)^2*
          (2:ℝ)^N*(9/4:ℝ)^2*scalar p)*
          (p.scale*Z^(∑ i,d.w i)*(sourceVolume p.source/pairNorm p.source.d))*Z^(2*cutoffLoss N ε) := by
        unfold coefficientZero
        ring
      _ ≤ (c.zero*selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*(profileCap d.root)^2*
          (2:ℝ)^N*(9/4:ℝ)^2*Kslot^(2*N))*((2:ℝ)^N*ref p)*Z^(firstLoss (N:=N) (ε:=ε)) := by
        gcongr
      _ = _ := by
        unfold rootZero
        have hn : (2:ℝ)^N*(2:ℝ)^N=(2:ℝ)^(2*N) := by rw [← pow_add]; congr 1; omega
        rw [show (2:ℝ)^(2*N)=(2:ℝ)^N*(2:ℝ)^N from hn.symm]
        ring
  · have hp : Z^(windowLoss ε) ≤ Z^(firstLoss (N:=N) (ε:=ε)) :=
      Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le (by unfold firstLoss; linarith)
    rw [coefficientNonexceptional,first_profile_core d p U tp]
    calc
      _ ≤ Kslot^(2*N)*(c.nonexceptional*(Kslot^(4*N)*(2:ℝ)^N/(1/4:ℝ)^2)*
          profileCore d.root Kslot N U.nonexceptionalDegree U.nonexceptionalControl d.t₀ tp d.V*
          ref p*Z^(firstLoss (N:=N) (ε:=ε))) := by
        gcongr
        exact base_le_reference p
      _ = _ := by unfold rootNonexceptional; ring
  · have hpaid : 19*cutoffLoss N ε-9*omegaLoss ε ≤ 0 := by
      have hi := (internal_spec N ε hε).2.2.1
      have ho := (omega_spec ε hε).1.le
      unfold cutoffLoss
      linarith
    have hp : Z^(2*cutoffLoss N ε)*Z^(-9*omegaLoss ε)*Z^(17*cutoffLoss N ε) ≤
        Z^(firstLoss (N:=N) (ε:=ε)) := by
      rw [← Real.rpow_add hz,← Real.rpow_add hz]
      apply Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le
      linarith
    have henvSq : (profileEnvelope p.source N Kslot U.exceptionalDegree U.exceptionalControl Z (cutoffLoss N ε))^2 =
        (profileEnvelope d.root N Kslot U.exceptionalDegree U.exceptionalControl 1 0)^2*Z^(2*cutoffLoss N ε) := by
      have hpower : (Z^(cutoffLoss N ε))^2 = Z^(2*cutoffLoss N ε) := by
        rw [pow_two, ← Real.rpow_add hz]
        congr 1
        ring
      rw [first_profile_envelope d p,mul_pow,hpower]
    have hslot := slot_shape_cap d hcard hKslot
    have hshapePaid : scalar p*shape (sourceVolume p.source) (pairNorm p.source.d)
        (prefixNormMax p.source.d) p.source.L p.scale 1 ≤
        (slotShapeCap (N:=N) (Kslot:=Kslot)*(2/9:ℝ)^(-2/3:ℝ))*ref p*Z^(-9*omegaLoss ε) := by
      apply hshape.trans
      gcongr
    calc
      _ = (c.exceptional*selectedCap N Kslot*heightBase tp^(2*U.exceptionalDegree)*
          (profileEnvelope d.root N Kslot U.exceptionalDegree U.exceptionalControl 1 0)^2)*
          (scalar p*shape (sourceVolume p.source) (pairNorm p.source.d) (prefixNormMax p.source.d) p.source.L p.scale 1)*
          Z^(2*cutoffLoss N ε)*Z^(17*cutoffLoss N ε) := by
        unfold coefficientExceptional
        rw [henvSq]
        ring
      _ ≤ (c.exceptional*selectedCap N Kslot*heightBase tp^(2*U.exceptionalDegree)*
          (profileEnvelope d.root N Kslot U.exceptionalDegree U.exceptionalControl 1 0)^2)*
          ((slotShapeCap (N:=N) (Kslot:=Kslot)*(2/9:ℝ)^(-2/3:ℝ))*ref p*Z^(-9*omegaLoss ε))*
          Z^(2*cutoffLoss N ε)*Z^(17*cutoffLoss N ε) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hshapePaid (by positivity))
            (Real.rpow_nonneg hz.le _)) (Real.rpow_nonneg hz.le _)
      _ = (rootExceptional d U c tp*ref p)*
          (Z^(2*cutoffLoss N ε)*Z^(-9*omegaLoss ε)*Z^(17*cutoffLoss N ε)) := by
        unfold rootExceptional
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hroots.2.2.1 href)
  · calc
      _ ≤ Kslot^(2*N)*(c.tail*selectedCap N Kslot*(profileCap d.root)^2*ref p) := by
        unfold coefficientTail
        gcongr
      _ = rootTail d c*ref p := by unfold rootTail; ring
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hroots.2.2.2 href) hZloss

theorem paid_budget (p : Point d) (U : Controls) (c : Constants) (tp : ℝ)
    (hε : 0 < ε) (hcard : Fintype.card ι ≤ N) (hKslot : 1 ≤ Kslot) (hevent : Event.{u} N ε Z) :
    scalar p*budget p U c tp ≤ rootBudget d U c tp*ref p*Z^(firstLoss (N:=N) (ε:=ε)) := by
  have h := paid_coefficients d p U c tp hε hcard hKslot hevent
  have he := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add h.1 h.2.1) h.2.2.1) h.2.2.2) (by norm_num : (0:ℝ) ≤ 256)
  convert he using 1 <;> dsimp only [budget,rootBudget] <;> ring

end
end Candidate.SilPrior.FourthPower.RepairedPaidFirstBudget
