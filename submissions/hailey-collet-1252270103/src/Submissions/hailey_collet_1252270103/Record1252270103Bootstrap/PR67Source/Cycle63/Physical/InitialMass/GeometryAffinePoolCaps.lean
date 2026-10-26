import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryAffineCaps
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentCommonRadialData
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentAmplificationChildSourceCaps Cycle63InitialSource
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
variable {Z Bmask bΦ a b : ℝ} (state : NaturalState Z Bmask bΦ) (p : Profiles a b) (ha : 0 < a)
variable (Lc M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "inp" => affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha Lc t X₁ X₂ hX₁ hX₂
local notation "V" => CenteredMomentAmplificationChildInput.volume inp

omit [DecidableEq ι] in
/-- Every stored prime or plain factor obeys one fixed polynomial cap,
including when another pool is empty. The threshold absorbs only fixed
support endpoints and precedes all live source parameters. -/
theorem affine_individual_pool_cap (Mmax : ℝ) (hZ : 1<Z)
    (hM : 0≤M) (hmax : M≤Mmax) (hb : 0≤b)
    (hbsZ : max 1 bslot≤Z) (hbZ : b≤Z)
    (hw : ∀i,0≤w i) (hLc₀ : 0≤Lc) (hLc : Lc≤M/4)
    (hvol : length Z X₁+length Z X₂+∑i,w i≤M) :
    ∀j I,I∈(inp).pools j→(I.absNorm:ℝ)≤Z^(Mmax+1) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hn₁ := length_nonneg Z X₁ hZ
  have hn₂ := length_nonneg Z X₂ hZ
  have hw0 : 0≤∑i,w i := Finset.sum_nonneg (fun i _=>hw i)
  have hscale := affine_plain_caps rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha Lc M t X₁ X₂ hX₁ hX₂ Mmax hZ hM hmax hLc₀ hLc (by linarith)
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
      (Nat.floor_le (by positivity : 0≤ max 1 bslot*Z^(w i)))
    have hi : w i≤∑j,w j := Finset.single_le_sum (fun j _=>hw j) (Finset.mem_univ i)
    have hi' : w i≤Mmax := by linarith
    calc
      (I.absNorm:ℝ)≤ max 1 bslot*Z^(w i) := hn
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
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
