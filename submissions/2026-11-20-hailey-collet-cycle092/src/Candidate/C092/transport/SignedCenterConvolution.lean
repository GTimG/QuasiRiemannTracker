/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.transport.SignedCenterWeights

/-! Convolution interpolation: an actual factored ordinary lattice estimate
with 1/L saving and an absolute count combine to the 3/5 saving. The final
source here is the explicit Euler-coefficient convolution; identification with
the manuscript's original jointly cube-free ideal sum is a separate boundary.
-/
set_option autoImplicit false
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentHeckeCancellation CenteredMomentHeckeTwist CenteredMomentTwist
open CenteredMomentHeckeHeight CenteredMomentLattice
local notation "O" => HeckeFamily.O

lemma min_one_rpow (x : ℝ) (hx : 0 < x) : min 1 x ≤ x^(3/5 : ℝ) := by
  by_cases h : x ≤ 1
  · rw [min_eq_right h]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hx h (by norm_num : (3/5 : ℝ) ≤ 1)
  · rw [min_eq_left (le_of_not_ge h)]
    exact Real.one_le_rpow (le_of_not_ge h) (by norm_num)

/-- The exact scalar interpolation which converts the numerator's critical
2/5 coefficient mass and ordinary 1/L saving into 3/5 saving. -/
theorem convolution_interpolation (d₁ d₂ L : ℝ) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hL : 0 < L) :
    (1/(d₁*d₂))*min 1 (max d₁ d₂/L) ≤
      (d₁*d₂)^(-(2/5 : ℝ))*L^(-(3/5 : ℝ)) := by
  have hp : 0 < d₁*d₂ := mul_pos (lt_of_lt_of_le zero_lt_one hd₁) (lt_of_lt_of_le zero_lt_one hd₂)
  have hmax : max d₁ d₂ ≤ d₁*d₂ := by
    apply max_le <;> nlinarith
  have hmin : min 1 (max d₁ d₂/L) ≤ ((d₁*d₂)/L)^(3/5 : ℝ) :=
    (min_le_min_left 1 (div_le_div_of_nonneg_right hmax hL.le)).trans
      (min_one_rpow _ (div_pos hp hL))
  calc
    _ ≤ (1/(d₁*d₂))*(((d₁*d₂)/L)^(3/5 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = (d₁*d₂)^(-(2/5 : ℝ))*L^(-(3/5 : ℝ)) := by
      rw [Real.div_rpow hp.le hL.le,Real.rpow_neg hL.le]
      have he : (d₁*d₂)^(3/5 : ℝ)/(d₁*d₂)=(d₁*d₂)^(-(2/5 : ℝ)) := by
        rw [←Real.rpow_sub_one hp.ne']
        norm_num
      calc
        _ = ((d₁*d₂)^(3/5 : ℝ)/(d₁*d₂))*(L^(3/5 : ℝ))⁻¹ := by ring
        _ = _ := by rw [he]

lemma raw_of_normalized (D : ℂ) (T A L : ℝ) (hT : 0 < T) (hL : 0 < L)
    (h : ‖(Real.sqrt T : ℂ)⁻¹*D‖ ≤ A*(Real.sqrt T/L)) :
    ‖D‖ ≤ A*(T/L) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hm := mul_le_mul_of_nonneg_left h hs.le
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hs.le,
    ←mul_assoc,mul_inv_cancel₀ hs.ne',one_mul] at hm
  have he : Real.sqrt T*(A*(Real.sqrt T/L))=A*(T/L) := by
    field_simp
    rw [Real.sq_sqrt hT.le]
    ring
  exact he ▸ hm

lemma normalized_of_raw (D : ℂ) (T A : ℝ) (hT : 0 < T) (h : ‖D‖ ≤ A*T) :
    ‖(Real.sqrt T : ℂ)⁻¹*D‖ ≤ A*Real.sqrt T := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hs.le]
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs.le)
  have he : (Real.sqrt T)⁻¹*(A*T)=A*Real.sqrt T := by
    field_simp
    rw [Real.sq_sqrt hT.le]
    ring
  exact he ▸ hm

/-- Fixed inducing row data, including the genuine full row identity. -/
structure OrdinaryRow where
  η : Character
  χ : Character
  ψ : Character
  Q : Ideal O
  hQ : Q ≠ 0
  hQψ : Q ≤ ψ.modulus
  hind : CenteredExceptionalProfile.InducedBy χ ψ
  m : O
  A : O
  z : O
  hml : ConcretePrimeRowBridge.goodLambda ∣ m
  hm2 : (2 : O) ∣ m
  hrow : ∀ n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
    (HeckeRowClosure.elementHom η) m 1 (A*z) n

structure OrdinaryProfile where
  W : ℝ → ℂ
  a : ℝ
  b : ℝ
  M : ℝ
  t : ℝ
  ha : 0 < a
  hb : 0 ≤ b
  hM : 0 ≤ M
  hs : Function.support W ⊆ Set.Icc a b
  hW : ContDiff ℝ ∞ W
  hbound : ∀ y,‖W y‖ ≤ M

def OrdinaryProfile.normalized (P : OrdinaryProfile) : 𝓢(ℝ,ℂ) :=
  normPowerProfile P.W P.a P.b P.ha P.hs P.hW P.t

def pairSource (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile) (x y : ℝ) : ℂ :=
  idealSum R₁.χ P₁.normalized x*idealSum R₂.χ P₂.normalized y

def pairC (P₁ P₂ : OrdinaryProfile) : ℝ := 128*(P₁.b*P₁.M+P₂.b*P₂.M)

def pairE (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile) : ℝ :=
  volumeControl R₁.Q R₁.χ P₁.normalized+volumeControl R₂.Q R₂.χ P₂.normalized

lemma pairC_nonneg (P₁ P₂ : OrdinaryProfile) : 0 ≤ pairC P₁ P₂ := by
  dsimp only [pairC]
  exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg P₁.hb P₁.hM) (mul_nonneg P₂.hb P₂.hM))

lemma pairE_nonneg (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile) : 0 ≤ pairE R₁ R₂ P₁ P₂ :=
  add_nonneg (volumeControl_nonneg _ _ _) (volumeControl_nonneg _ _ _)

lemma pairSource_absolute (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    ‖pairSource R₁ R₂ P₁ P₂ x y‖ ≤ (pairC P₁ P₂)^2*(x*y) := by
  have h₁ := idealSum_absolute R₁.χ P₁.normalized P₁.b P₁.M x P₁.hb P₁.hM hx
    (fun u => (normPowerProfile_norm P₁.W P₁.a P₁.b P₁.ha P₁.hs P₁.hW P₁.t u).trans_le (P₁.hbound u))
    ((normPowerProfile_support P₁.W P₁.a P₁.b P₁.ha P₁.hs P₁.hW P₁.t).trans (fun _ hu => (P₁.hs hu).2))
  have h₂ := idealSum_absolute R₂.χ P₂.normalized P₂.b P₂.M y P₂.hb P₂.hM hy
    (fun u => (normPowerProfile_norm P₂.W P₂.a P₂.b P₂.ha P₂.hs P₂.hW P₂.t u).trans_le (P₂.hbound u))
    ((normPowerProfile_support P₂.W P₂.a P₂.b P₂.ha P₂.hs P₂.hW P₂.t).trans (fun _ hu => (P₂.hs hu).2))
  have hc₁ : 128*P₁.b*P₁.M ≤ pairC P₁ P₂ := by dsimp only [pairC]; nlinarith [mul_nonneg P₂.hb P₂.hM]
  have hc₂ : 128*P₂.b*P₂.M ≤ pairC P₁ P₂ := by dsimp only [pairC]; nlinarith [mul_nonneg P₁.hb P₁.hM]
  have ha₁ := h₁.trans (mul_le_mul_of_nonneg_right hc₁ hx.le)
  have ha₂ := h₂.trans (mul_le_mul_of_nonneg_right hc₂ hy.le)
  rw [pairSource,norm_mul]
  exact (mul_le_mul ha₁ ha₂ (norm_nonneg _) (mul_nonneg (pairC_nonneg _ _) hx.le)).trans_eq (by ring)

lemma pairSource_signed (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖pairSource R₁ R₂ P₁ P₂ X₁ X₂-pairSource R₁ R₂ P₁ P₂ Y₁ Y₂‖ ≤
      (4*pairE R₁ R₂ P₁ P₂*pairC P₁ P₂)*(T/L) := by
  have h := distinct_fixedrow_factored_centering
    R₁.η R₁.χ R₁.ψ R₂.η R₂.χ R₂.ψ R₁.Q R₂.Q R₁.hQ R₂.hQ R₁.hQψ R₂.hQψ R₁.hind R₂.hind
    R₁.m R₁.A R₁.z R₂.m R₂.A R₂.z R₁.hml R₁.hm2 R₂.hml R₂.hm2 R₁.hrow R₂.hrow
    P₁.W P₂.W P₁.a P₁.b P₂.a P₂.b P₁.M P₂.M P₁.ha P₂.ha P₁.hb P₂.hb P₁.hM P₂.hM
    P₁.hs P₂.hs P₁.hW P₂.hW P₁.hbound P₂.hbound P₁.t P₂.t X₁ X₂ Y₁ Y₂ T L
    hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  exact raw_of_normalized _ T _ L (hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)) hL h

def pairK (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile) : ℝ :=
  2*(pairC P₁ P₂)^2+4*pairE R₁ R₂ P₁ P₂*pairC P₁ P₂

lemma pairK_nonneg (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile) : 0 ≤ pairK R₁ R₂ P₁ P₂ := by
  dsimp only [pairK]
  exact add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by norm_num) (pairE_nonneg _ _ _ _)) (pairC_nonneg _ _))

/-- The actual lattice source, after any two extracted nonzero ideals, already
has the precise termwise 3/5 estimate needed by the global coefficient series. -/
theorem pairSource_scaled_saving (R₁ R₂ : OrdinaryRow) (P₁ P₂ : OrdinaryProfile)
    (d₁ d₂ X₁ X₂ Y₁ Y₂ T L : ℝ) (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖pairSource R₁ R₂ P₁ P₂ (X₁/d₁) (X₂/d₂)-
      pairSource R₁ R₂ P₁ P₂ (Y₁/d₁) (Y₂/d₂)‖ ≤
    pairK R₁ R₂ P₁ P₂*T*(d₁*d₂)^(-(2/5 : ℝ))*L^(-(3/5 : ℝ)) := by
  have hd₁p : 0 < d₁ := zero_lt_one.trans_le hd₁
  have hd₂p : 0 < d₂ := zero_lt_one.trans_le hd₂
  have hp : 0 < d₁*d₂ := mul_pos hd₁p hd₂p
  have hm : 0 < max d₁ d₂ := hd₁p.trans_le (le_max_left _ _)
  have hℓ : 0 < L/max d₁ d₂ := div_pos hL hm
  have hs₁ (X : ℝ) (hX : L ≤ X) : L/max d₁ d₂ ≤ X/d₁ :=
    (div_le_div_of_nonneg_left hL.le hd₁p (le_max_left _ _)).trans
      (div_le_div_of_nonneg_right hX hd₁p.le)
  have hs₂ (X : ℝ) (hX : L ≤ X) : L/max d₁ d₂ ≤ X/d₂ :=
    (div_le_div_of_nonneg_left hL.le hd₂p (le_max_right _ _)).trans
      (div_le_div_of_nonneg_right hX hd₂p.le)
  have hpX' : (X₁/d₁)*(X₂/d₂)=T/(d₁*d₂) := by rw [div_mul_div_comm,hpX]
  have hpY' : (Y₁/d₁)*(Y₂/d₂)=T/(d₁*d₂) := by rw [div_mul_div_comm,hpY]
  have hT : 0 < T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hK₁ : 2*(pairC P₁ P₂)^2 ≤ pairK R₁ R₂ P₁ P₂ := by
    dsimp only [pairK]
    have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (pairE_nonneg R₁ R₂ P₁ P₂)) (pairC_nonneg P₁ P₂)
    linarith
  have hK₂ : 4*pairE R₁ R₂ P₁ P₂*pairC P₁ P₂ ≤ pairK R₁ R₂ P₁ P₂ := by dsimp only [pairK]; nlinarith [sq_nonneg (pairC P₁ P₂)]
  have habs : ‖pairSource R₁ R₂ P₁ P₂ (X₁/d₁) (X₂/d₂)-
      pairSource R₁ R₂ P₁ P₂ (Y₁/d₁) (Y₂/d₂)‖ ≤ pairK R₁ R₂ P₁ P₂*(T/(d₁*d₂)) := by
    have ha := pairSource_absolute R₁ R₂ P₁ P₂ _ _
      (div_pos (hL.trans_le hX₁) hd₁p) (div_pos (hL.trans_le hX₂) hd₂p)
    have hb := pairSource_absolute R₁ R₂ P₁ P₂ _ _
      (div_pos (hL.trans_le hY₁) hd₁p) (div_pos (hL.trans_le hY₂) hd₂p)
    rw [hpX'] at ha
    rw [hpY'] at hb
    exact (norm_sub_le _ _).trans ((add_le_add ha hb).trans
      ((by ring_nf : (pairC P₁ P₂)^2*(T/(d₁*d₂))+(pairC P₁ P₂)^2*(T/(d₁*d₂)) =
        (2*(pairC P₁ P₂)^2)*(T/(d₁*d₂))) ▸
        mul_le_mul_of_nonneg_right hK₁ (div_nonneg hT.le hp.le)))
  have hsign := pairSource_signed R₁ R₂ P₁ P₂ _ _ _ _ _ _ hℓ
    (hs₁ _ hX₁) (hs₂ _ hX₂) (hs₁ _ hY₁) (hs₂ _ hY₂) hpX' hpY'
  have he : (T/(d₁*d₂))/(L/max d₁ d₂)=(T/(d₁*d₂))*(max d₁ d₂/L) := by field_simp
  rw [he] at hsign
  have hsign' := hsign.trans (mul_le_mul_of_nonneg_right hK₂
    (mul_nonneg (div_nonneg hT.le hp.le) (div_nonneg hm.le hL.le)))
  have hboth : ‖pairSource R₁ R₂ P₁ P₂ (X₁/d₁) (X₂/d₂)-
      pairSource R₁ R₂ P₁ P₂ (Y₁/d₁) (Y₂/d₂)‖ ≤
      pairK R₁ R₂ P₁ P₂*T*((1/(d₁*d₂))*min 1 (max d₁ d₂/L)) := by
    by_cases h : max d₁ d₂/L ≤ 1
    · rw [min_eq_right h]
      convert hsign' using 1 <;> ring
    · rw [min_eq_left (le_of_not_ge h)]
      convert habs using 1 <;> ring
  exact hboth.trans ((mul_le_mul_of_nonneg_left (convolution_interpolation d₁ d₂ L hd₁ hd₂ hL)
    (mul_nonneg (pairK_nonneg _ _ _ _) hT.le)).trans_eq (by ring))

end
end QRH.Cycle092.SignedCenter
