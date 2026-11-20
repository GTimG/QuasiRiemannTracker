/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussPhysicalSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open QRH.Cycle092.SignedCenter
open CenteredMomentLattice CenteredMomentTwist
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- Original Schwartz profile with its actual independently chosen height.
The bound is its native Schwartz seminorm, not an extra profile assumption. -/
def actualOrdinaryProfile (W : SchwartzMap ℝ ℂ) (ha : 0<a) (hb : 0≤b)
    (hs : Function.support W⊆Set.Icc a b) (t : ℝ) : OrdinaryProfile where
  W:=W
  a:=a
  b:=b
  M:=SchwartzMap.seminorm ℝ 0 0 W
  t:=t
  ha:=ha
  hb:=hb
  hM:=(norm_nonneg (W 0)).trans (SchwartzMap.norm_le_seminorm ℝ W 0)
  hs:=hs
  hW:=W.smooth ⊤
  hbound:=SchwartzMap.norm_le_seminorm ℝ W

def actualProfile₁ (r : Source ι a b) (ha : 0<a) (hb : 0≤b) (v : ℝ) : OrdinaryProfile :=
  actualOrdinaryProfile r.W₁ ha hb r.hs₁ (r.t₁+v)

def actualProfile₂ (r : Source ι a b) (ha : 0<a) (hb : 0≤b) (v : ℝ) : OrdinaryProfile :=
  actualOrdinaryProfile r.W₂ ha hb r.hs₂ (r.t₂+v)

lemma actualOrdinaryProfile_shift (W : SchwartzMap ℝ ℂ) (ha : 0<a) (hb : 0≤b)
    (hs : Function.support W⊆Set.Icc a b) (t v : ℝ) :
    QRH.SilDensitySplit.CubeFree.FP.ReferencePrimeEnclosure.phaseProfile
      (normPowerProfile W a b ha hs (W.smooth ⊤) t) (v/(2*Real.pi))=
      (actualOrdinaryProfile W ha hb hs (t+v)).normalized := by
  funext x
  change _=(normPowerProfile W a b ha hs (W.smooth ⊤) (t+v)) x
  simp only [QRH.SilDensitySplit.CubeFree.FP.ReferencePrimeEnclosure.phaseProfile,
    normPowerProfile_apply]
  by_cases hx : 0<x
  · rw [logPhase_eq_normPower v x hx]
    simp only [Complex.ofReal_add,mul_add,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    ring
  · have hw : W x=0 := by
      by_contra hh
      exact hx (lt_of_lt_of_le ha (hs hh).1)
    simp only [hw,mul_zero,zero_mul]

lemma shiftedProfile₁_eq_actual (r : Source ι a b) (ha : 0<a) (hb : 0≤b) (v : ℝ) :
    shiftedProfile₁ r ha v=(actualProfile₁ r ha hb v).normalized :=
  actualOrdinaryProfile_shift r.W₁ ha hb r.hs₁ r.t₁ v

lemma shiftedProfile₂_eq_actual (r : Source ι a b) (ha : 0<a) (hb : 0≤b) (v : ℝ) :
    shiftedProfile₂ r ha v=(actualProfile₂ r ha hb v).normalized :=
  actualOrdinaryProfile_shift r.W₂ ha hb r.hs₂ r.t₂ v

#print axioms shiftedProfile₁_eq_actual
#print axioms shiftedProfile₂_eq_actual

end
end QRH.Cycle092.FixedCubeGauss
