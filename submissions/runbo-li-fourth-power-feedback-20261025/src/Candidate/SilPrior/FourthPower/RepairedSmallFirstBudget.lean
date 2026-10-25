/- Copyright (c) 2026 Sil. Apache-2.0.
The actual four empty-selected shapes paid at the first common reference.
Both original common norms and the canonical allowance are retained.
No analytic hypothesis is introduced.
-/
import Candidate.SilPrior.FourthPower.RepairedSmallPoint
import Candidate.SilPrior.FourthPower.RepairedSmallShapeRawCost
import Candidate.SilPrior.FourthPower.RepairedPaidFirstBudget

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedSmallFirstBudget
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedFirstExceptionalNormalization MixedInnerExceptionalBlock MixedPrincipalCentered
open RepairedRootParameters RepairedRawContext RepairedFirstPoint RepairedRootCaps RepairedCapEvent
open RepairedFirstScalarBudget RepairedSmallPoint RepairedSmallShapeRawCost
open QRH.Record1252270103KernelMass
open CenteredMomentFirstMixedAllowance
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤H}
variable {ι : Type u} [Fintype ι] {Wslot : ℝ→ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ}
variable {η η₀ : Character} {d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀}

def zeroBudget (p : Point d) : ℝ :=
  (9/4:ℝ)^2*(2:ℝ)^N*p.scale*(sourceVolume p.source/pairNorm p.source.d)*Z^(zeroLoss N ε)
def nativeBudget (p : Point d) : ℝ :=
  sigmaFixed*(2:ℝ)^N*(p.tau.modulus.absNorm:ℝ)*(sourceVolume p.source/pairNorm p.source.d)^2*
    Z^(nativeLoss N ε)
def exceptionalBudget (p : Point d) : ℝ :=
  (1/4:ℝ)^(-4/3:ℝ)*shape (sourceVolume p.source) (pairNorm p.source.d)
    (prefixNormMax p.source.d) p.source.L p.scale 1*Z^(exceptionalLoss N ε)
def tailBudget : ℝ := Z^(-(40:ℝ))
def geometryBudget (p : Point d) : ℝ :=
  zeroBudget p+nativeBudget p+exceptionalBudget p+tailBudget (Z:=Z)

def firstLoss (N : ℕ) (ε : ℝ) : ℝ := (3/4:ℝ)*widthFloor ε+19*cutoffLoss N ε
def zeroConstant (N : ℕ) (Kslot : ℝ) : ℝ := (9/4:ℝ)^2*((2:ℝ)^N)^2*Kslot^(2*N)
def nativeConstant (N : ℕ) (Kslot : ℝ) : ℝ := sigmaFixed*(2:ℝ)^N*((2:ℝ)^N)^2*Kslot^(2*N)
def exceptionalConstant (N : ℕ) (Kslot : ℝ) : ℝ :=
  (1/4:ℝ)^(-4/3:ℝ)*RepairedPaidFirstBudget.slotShapeCap (N:=N) (Kslot:=Kslot)*(2/9:ℝ)^(-2/3:ℝ)
def geometryConstant (N : ℕ) (Kslot : ℝ) : ℝ :=
  zeroConstant N Kslot+nativeConstant N Kslot+exceptionalConstant N Kslot+Kslot^(2*N)

theorem budget_nonneg (p : Point d) : 0≤geometryBudget p := by
  have hz := zero_lt_one.trans d.one_lt_Z
  have hV:=(sourceVolume_pos p.source).le
  have hp:=(pairNorm_pos p.source.hd.1 p.source.hd.2).le
  have hK : 0<p.scale:=Real.rpow_pos_of_pos (zero_lt_one.trans d.one_lt_Z) _
  have hshape : 0≤shape (sourceVolume p.source) (pairNorm p.source.d)
    (prefixNormMax p.source.d) p.source.L p.scale 1 := by
    have hL:=p.source.hL
    have hH:=prefixNormMax_pos p.source.d p.source.hd
    unfold shape
    positivity
  have hsig : 0≤sigmaFixed:=by unfold sigmaFixed; positivity
  unfold geometryBudget zeroBudget nativeBudget exceptionalBudget tailBudget
  positivity

theorem constant_pos (N : ℕ) (Kslot : ℝ) (hKslot : 1≤Kslot) : 0<geometryConstant N Kslot := by
  have hK : 0<Kslot:=zero_lt_one.trans_le hKslot
  have hsig : 0≤sigmaFixed:=by unfold sigmaFixed; positivity
  unfold geometryConstant zeroConstant nativeConstant exceptionalConstant RepairedPaidFirstBudget.slotShapeCap
  positivity

theorem loss_nonneg (N : ℕ) (ε : ℝ) (hε : 0<ε) : 0≤firstLoss N ε := by
  have hf:0<widthFloor ε:=(mesh_spec ε hε).1
  have hδ:=(internal_losses_paid N ε hε).1
  unfold firstLoss
  positivity

theorem total_loss_paid (N : ℕ) (ε : ℝ) (hε : 0<ε) : firstLoss N ε+10*cutoffLoss N ε≤ε/4 := by
  have hf : widthFloor ε≤ε/1024:=(mesh_spec ε hε).2.2
  have hi:=(internal_spec N ε hε).2.2.1
  have ho:=(omega_spec ε hε).2.2.1
  unfold firstLoss cutoffLoss
  linarith

theorem paid_geometry (p : Point d) (hε : 0<ε) (hcard : Fintype.card ι≤N)
    (hKslot : 1≤Kslot) (hevent : Event.{u} N ε Z) :
    scalar p*geometryBudget p≤geometryConstant N Kslot*ref p*Z^(firstLoss N ε) := by
  have hz:=zero_lt_one.trans d.one_lt_Z
  have hf:=frozen_scalar_cap p hcard hKslot
  have hv:=first_volume_cap p hcard
  have hS:0≤∑i,d.w i:=d.hface.1
  have hZS:1≤Z^(∑i,d.w i):=Real.one_le_rpow d.one_lt_Z.le hS
  have hδ:=(internal_losses_paid N ε hε).1
  have hfloor:0<widthFloor ε:=(mesh_spec ε hε).1
  have hω:=(omega_spec ε hε).1
  have hK : 0<p.scale:=Real.rpow_pos_of_pos hz _
  have hV:=(sourceVolume_pos p.source).le
  have hp:=(pairNorm_pos p.source.hd.1 p.source.hd.2).le
  have hscalar:0≤scalar p:=sq_nonneg _
  have href:0≤ref p:=(ref_pos p).le
  have hsig:0≤sigmaFixed:=by unfold sigmaFixed; positivity
  have hLoss:=loss_nonneg N ε hε
  have hZloss:1≤Z^(firstLoss N ε):=Real.one_le_rpow d.one_lt_Z.le hLoss
  have hzn:Z^(nativeLoss N ε)≤Z^(firstLoss N ε):=
    Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le (by unfold nativeLoss firstLoss; linarith)
  have hzz:Z^(zeroLoss N ε)≤Z^(firstLoss N ε):=
    Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le (by unfold zeroLoss firstLoss; linarith)
  have hzero:scalar p*zeroBudget p≤zeroConstant N Kslot*ref p*Z^(firstLoss N ε) := by
    have hpaid:=zero_geometry_reference p hε hcard hevent
    have hplain:p.scale*(sourceVolume p.source/pairNorm p.source.d)≤(2:ℝ)^N*ref p := by
      calc
        _≤p.scale*Z^(∑i,d.w i)*(sourceVolume p.source/pairNorm p.source.d) := by
          nlinarith [mul_nonneg hK.le (div_nonneg hV hp)]
        _≤_:=hpaid
    calc
      _=((9/4:ℝ)^2*(2:ℝ)^N*scalar p)*(p.scale*(sourceVolume p.source/pairNorm p.source.d))*Z^(zeroLoss N ε) := by
        unfold zeroBudget; ring
      _≤((9/4:ℝ)^2*(2:ℝ)^N*Kslot^(2*N))*((2:ℝ)^N*ref p)*Z^(firstLoss N ε) := by gcongr
      _=_:=by unfold zeroConstant; ring
  have hnative:scalar p*nativeBudget p≤nativeConstant N Kslot*ref p*Z^(firstLoss N ε) := by
    have hbase:(p.tau.modulus.absNorm:ℝ)*(sourceVolume d.root/(p.label.val.1.absNorm:ℝ))^2≤ref p := by
      unfold ref MixedFirstExceptionalNormalization.reference
      apply le_mul_of_one_le_right (by positivity)
      exact Real.one_le_rpow d.one_lt_Z.le (allowance_nonneg _ _ _)
    have hv2 : (sourceVolume p.source/pairNorm p.source.d)^2≤
        ((2:ℝ)^N)^2*(sourceVolume d.root/(p.label.val.1.absNorm:ℝ))^2 := by
      have hh:=pow_le_pow_left₀ (div_nonneg hV hp) hv 2
      convert hh using 1 <;> ring
    calc
      _=(sigmaFixed*(2:ℝ)^N*scalar p)*(p.tau.modulus.absNorm:ℝ)*
          (sourceVolume p.source/pairNorm p.source.d)^2*Z^(nativeLoss N ε) := by unfold nativeBudget; ring
      _≤(sigmaFixed*(2:ℝ)^N*Kslot^(2*N))*(p.tau.modulus.absNorm:ℝ)*
          (((2:ℝ)^N)^2*(sourceVolume d.root/(p.label.val.1.absNorm:ℝ))^2)*Z^(firstLoss N ε) := by gcongr
      _=(sigmaFixed*(2:ℝ)^N*Kslot^(2*N)*((2:ℝ)^N)^2)*
          ((p.tau.modulus.absNorm:ℝ)*(sourceVolume d.root/(p.label.val.1.absNorm:ℝ))^2)*Z^(firstLoss N ε) := by ring
      _≤(sigmaFixed*(2:ℝ)^N*Kslot^(2*N)*((2:ℝ)^N)^2)*ref p*Z^(firstLoss N ε) := by gcongr
      _=_:=by unfold nativeConstant; ring
  have hex:scalar p*exceptionalBudget p≤exceptionalConstant N Kslot*ref p*Z^(firstLoss N ε) := by
    have hpaid:=exceptional_shape_reference p hε hevent
    have hslot:=RepairedPaidFirstBudget.slot_shape_cap d hcard hKslot
    have hpaid' : scalar p*shape (sourceVolume p.source) (pairNorm p.source.d)
        (prefixNormMax p.source.d) p.source.L p.scale 1 ≤
        (RepairedPaidFirstBudget.slotShapeCap (N:=N) (Kslot:=Kslot)*
          (2/9:ℝ)^(-2/3:ℝ))*ref p*Z^(-9*omegaLoss ε) := by
      apply hpaid.trans
      gcongr
    have hepow:Z^(-9*omegaLoss ε)*Z^(exceptionalLoss N ε)≤Z^(firstLoss N ε) := by
      rw [←Real.rpow_add hz]
      apply Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le
      unfold exceptionalLoss firstLoss
      linarith
    calc
      _=(1/4:ℝ)^(-4/3:ℝ)*(scalar p*shape (sourceVolume p.source) (pairNorm p.source.d)
          (prefixNormMax p.source.d) p.source.L p.scale 1)*Z^(exceptionalLoss N ε) := by unfold exceptionalBudget; ring
      _≤(1/4:ℝ)^(-4/3:ℝ)*((RepairedPaidFirstBudget.slotShapeCap (N:=N) (Kslot:=Kslot)*
          (2/9:ℝ)^(-2/3:ℝ))*ref p*Z^(-9*omegaLoss ε))*Z^(exceptionalLoss N ε) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpaid' (Real.rpow_nonneg (by norm_num) _))
          (Real.rpow_nonneg hz.le _)
      _=(exceptionalConstant N Kslot*ref p)*(Z^(-9*omegaLoss ε)*Z^(exceptionalLoss N ε)) := by
        unfold exceptionalConstant; ring
      _≤_:=mul_le_mul_of_nonneg_left hepow (by unfold exceptionalConstant RepairedPaidFirstBudget.slotShapeCap; positivity)
  have htail:scalar p*tailBudget (Z:=Z)≤Kslot^(2*N)*ref p*Z^(firstLoss N ε) := by
    have ht:=tail_power_reference p hε hcard hevent
    calc
      _≤Kslot^(2*N)*ref p:=mul_le_mul hf ht (Real.rpow_nonneg hz.le _) (by positivity)
      _≤_:=le_mul_of_one_le_right (by positivity) hZloss
  have hsum:=add_le_add (add_le_add (add_le_add hzero hnative) hex) htail
  convert hsum using 1 <;> simp only [geometryBudget,geometryConstant] <;> ring

end
end Candidate.SilPrior.FourthPower.RepairedSmallFirstBudget
