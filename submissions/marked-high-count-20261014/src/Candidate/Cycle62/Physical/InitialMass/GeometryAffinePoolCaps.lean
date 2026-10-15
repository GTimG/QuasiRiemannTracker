/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.GeometryAffineCaps

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentCommonRadialData
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentAmplificationChildSourceCaps Cycle62InitialSource
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
section Affine
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance geometryAffinePoolCapsFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters rayM H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z bΦ a b : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles a b) (ha : 0 < a)
variable (M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "inp" => affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂
local notation "V" => CenteredMomentAmplificationChildInput.volume inp


omit [DecidableEq ι] in
/-- Every stored prime or plain factor obeys one fixed polynomial cap,
including when another pool is empty. The threshold absorbs only fixed
support endpoints and precedes all live source parameters. -/
theorem affine_individual_pool_cap (Mmax : ℝ) (hZ : 1<Z)
    (hM : 0≤M) (hmax : M≤Mmax) (hb : 0≤b)
    (hbsZ : max 1 bslot≤Z) (hbZ : b≤Z)
    (hw : ∀i,0≤w i) (hslots : (∑i,w i)≤M/25)
    (hhi₁ : length Z X₁≤(44/100)*M) (hhi₂ : length Z X₂≤(44/100)*M) :
    ∀j I,I∈(inp).pools j→(I.absNorm:ℝ)≤Z^(Mmax+1) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hscale := affine_plain_caps rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂ Mmax hZ hM hmax hhi₁ hhi₂
  have hpay (X : ℝ) (hx : X≤Z^Mmax) : b*X≤Z^(Mmax+1) := by
    calc
      _≤b*Z^Mmax := mul_le_mul_of_nonneg_left hx hb
      _≤Z*Z^Mmax := mul_le_mul_of_nonneg_right hbZ (Real.rpow_nonneg hz.le _)
      _=Z^(Mmax+1) := by
        calc
          Z*Z^Mmax=Z^(1:ℝ)*Z^Mmax := by rw [Real.rpow_one]
          _=Z^(1+Mmax) := (Real.rpow_add hz _ _).symm
          _=Z^(Mmax+1) := by congr 1;ring
  apply actual_completed_pool_cap inp (Z^(Mmax+1))
  · intro i I hI
    change I∈CenteredMomentPrimeSlot.primePool rayM H bslot (Z^(w i)) at hI
    have hn := (Nat.cast_le.mpr (mem_idealsUpTo.mp (Finset.mem_filter.mp hI).1).2).trans
      (Nat.floor_le (by positivity : 0≤max 1 bslot*Z^(w i)))
    have hi : w i≤∑j,w j := Finset.single_le_sum (fun j _=>hw j) (Finset.mem_univ i)
    have hi' : w i≤Mmax := by linarith
    calc
      (I.absNorm:ℝ)≤max 1 bslot*Z^(w i) := hn
      _≤Z*Z^Mmax := mul_le_mul hbsZ
        (Real.rpow_le_rpow_of_exponent_le hZ.le hi')
        (Real.rpow_nonneg hz.le _) hz.le
      _=Z^(Mmax+1) := by
        calc
          Z*Z^Mmax=Z^(1:ℝ)*Z^Mmax := by rw [Real.rpow_one]
          _=Z^(1+Mmax) := (Real.rpow_add hz _ _).symm
          _=Z^(Mmax+1) := by congr 1;ring
  · rfl
  · rfl
  · exact hpay _ (hscale false 0)
  · exact hpay _ (hscale true 0)
  · exact hpay _ (hscale false 1)
  · exact hpay _ (hscale true 1)
end Affine

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.affine_individual_pool_cap
