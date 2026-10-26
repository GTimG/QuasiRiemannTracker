/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The collected LOW mask contains only the fixed anchor, fixed external L and
actual Newton assignment. No moving first-common ideal is inserted. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.NewtonFrozenGeometry
import Submissions.hailey_collet_1252270103.Record12518109Raw.Context
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.RegularLowCollectedMask
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentSecondHeightFamily
open Record12518109Raw OAI.SevenEighths.Record1252270103Source QRH.Record1252270103Low
local notation "O" => HeckeFamily.O

theorem newton_pair_norm_cap (P S A : Finset (Ideal O)) (hS : S⊆P) (hA : A⊆S)
    (depth : ℕ) (hdepth : S.card≤depth) (Z a : ℝ) (hZ : 1≤Z) (ha : 0≤a)
    (hpool : ∀p∈P,(p.absNorm:ℝ)≤Z^a) :
    (((newtonDivisorPair S A).1*(newtonDivisorPair S A).2).absNorm:ℝ)≤Z^((depth:ℝ)*a) := by
  simpa only [one_mul,mul_one,map_one,Nat.cast_one,Real.rpow_zero,zero_add] using
    newton_frozen_norm_bound P S A hS hA depth hdepth 1 1 Z 0 a hZ ha (by simp) hpool

theorem newton_pair_nonzero (P S A : Finset (Ideal O)) (hS : S⊆P) (hA : A⊆S)
    (hp : ∀p∈P,p≠0) : (newtonDivisorPair S A).1*(newtonDivisorPair S A).2≠0 := by
  rw [newtonDivisorPair_product S A hA]
  exact Finset.prod_ne_zero_iff.mpr (fun p hpS=>hp p (hS hpS))

/-- Only the fixed arithmetic anchor and puncture determine the threshold.
The exponent is independent of ambient slot count and of moving common labels. -/
theorem eventually_collected_mask_cap (ηanchor : Character) (R₀ : Ideal O)
    (hR₀ : R₀≠0) (ηmaskBase : ℝ) (hηmaskBase : 0<ηmaskBase) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(ι : Type)[Fintype ι](s : Input ι),s.η=ηanchor →
      ∀L : Ideal O,L≠0 → (L.absNorm:ℝ)≤Z^(4:ℝ) →
      ∀(P S A : Finset (Ideal O))(depth : ℕ)(a : ℝ),S⊆P → A⊆S → S.card≤depth →
        0≤a → (∀p∈P,p≠0) → (∀p∈P,(p.absNorm:ℝ)≤Z^a) →
      (geometryRawFixedMask s R₀*L)*((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)≠0 ∧
      (((geometryRawFixedMask s R₀*L)*
        ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)).absNorm:ℝ)≤
        Z^(4+(depth:ℝ)*a+ηmaskBase) := by
  let fixed := ηanchor.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*R₀
  filter_upwards [(tendsto_rpow_atTop hηmaskBase).eventually
    (eventually_ge_atTop (fixed.absNorm:ℝ)),eventually_gt_atTop (1:ℝ)] with Z hfixed hZ
  refine ⟨hZ,?_⟩
  intro ι _ s hη L hL hLcap P S A depth a hS hA hdepth ha hp hpool
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hmask := geometry_raw_fixed_mask_ne_zero s R₀ hR₀
  have hpair := newton_pair_nonzero P S A hS hA hp
  refine ⟨mul_ne_zero (mul_ne_zero hmask hL) hpair,?_⟩
  have hfixed' : ((geometryRawFixedMask s R₀).absNorm:ℝ)≤Z^ηmaskBase := by
    simpa only [geometryRawFixedMask,hη,fixed] using hfixed
  have hbase : ((geometryRawFixedMask s R₀*L).absNorm:ℝ)≤Z^(4+ηmaskBase) := by
    rw [map_mul,Nat.cast_mul]
    apply (mul_le_mul hfixed' hLcap (Nat.cast_nonneg _) (Real.rpow_nonneg hZp.le _)).trans_eq
    rw [←Real.rpow_add hZp]
    congr 1
    ring
  have hnorm := newton_frozen_norm_bound P S A hS hA depth hdepth
    (geometryRawFixedMask s R₀*L) 1 Z (4+ηmaskBase) a hZ.le ha (by simpa using hbase) hpool
  simpa only [mul_one,one_mul,mul_assoc,show (4+ηmaskBase)+(depth:ℝ)*a=4+(depth:ℝ)*a+ηmaskBase by ring] using hnorm

end
end QRH.Record1252270103Source.RegularLowCollectedMask
#print axioms QRH.Record1252270103Source.RegularLowCollectedMask.newton_pair_norm_cap
#print axioms QRH.Record1252270103Source.RegularLowCollectedMask.newton_pair_nonzero
#print axioms QRH.Record1252270103Source.RegularLowCollectedMask.eventually_collected_mask_cap
