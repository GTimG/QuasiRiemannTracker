/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Q's strict volume collar pays the actual second zero and counted tail. -/
import Candidate.C092.transport.RootColoredSeedTerms
import Candidate.C092.transport.RawSidesZeroTailQ

set_option autoImplicit false
namespace QRH.Cycle092.RootColoredSeed
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceMass
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow
open MixedOriginalNormCap MixedOriginalTail
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- Q's zero-mode estimate has a fixed positive saving against `K*Z`.
    The seed harmonic sum is discharged, including its actual norm cap. -/
theorem zero_terms_Q (N : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type) [Fintype ι] (a b : ℝ) (r : Source ι a b), Fintype.card ι ≤ N →
    ∀ (ha : 0 < a) (η₁ η₂ : Character) (V : Finset Id) (hV : ∀ v ∈ V, v ≠ 0)
      (ψ : Character) (t Z K W : ℝ), 3 ≤ Z → 0 ≤ K → 0 ≤ W → W ≤ Z^(1/1000:ℝ) →
      sourceNormCap r.P b r.T r.d ≤ Z^(919/1000:ℝ) →
      (∀ v ∈ V, (v.absNorm : ℝ) ≤ Z^(8:ℝ)) →
      zeroTerms r ha (idealCoeff η₁) (idealCoeff η₂) V ψ t (16*K*W^4) ≤ C * profileCap r^2 * K * Z^(93/100:ℝ) := by
  obtain ⟨C0,hC0,h⟩ := zero_terms_bound N (1/1000) (by norm_num)
  let F := ‖EisensteinSchwartzPoisson.paperRadialFourier ballProfile 0‖
  let D : ℝ := 16*F*C0*2304*8*1000
  refine ⟨D+1,by dsimp [D,F]; positivity,?_⟩
  intro ι _ a b r hN ha η₁ η₂ V hV ψ t Z K W hZ hK hW hWcap hcap hVcap
  have hZ1 : 1 ≤ Z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hZ8 : 3 ≤ Z^(8:ℝ) := hZ.trans (by
    calc Z = Z^(1:ℝ) := (Real.rpow_one Z).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num))
  have hlog0 : 0 ≤ Real.log (Z^(8:ℝ)) := Real.log_nonneg (by linarith : 1 ≤ Z^(8:ℝ))
  have hW4 : W^4 ≤ Z^(4/1000:ℝ) := by
    calc W^4 ≤ (Z^(1/1000:ℝ))^4 := pow_le_pow_left₀ hW hWcap _
      _ = Z^(4/1000:ℝ) := by rw [← Real.rpow_mul_natCast hZ0.le]; norm_num
  have hlog : Real.log (Z^(8:ℝ)) ≤ 8*(Z^(1/1000:ℝ)/(1/1000:ℝ)) := by
    rw [Real.log_rpow hZ0]
    exact mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hZ0.le (by norm_num)) (by norm_num)
  have hb := h ι a b r hN ha η₁ η₂ V hV ψ t (16*K*W^4) (Z^(919/1000:ℝ)) (Z^(8:ℝ))
    (by positivity) (Real.one_le_rpow hZ1 (by norm_num)) hZ8 hcap hVcap
  have hpow : (Z^(919/1000:ℝ))^(1+(1/1000:ℝ)) = Z^((919/1000:ℝ)*(1+1/1000)) := by
    rw [← Real.rpow_mul hZ0.le]
  apply hb.trans
  calc
    _ ≤ (16*K*Z^(4/1000:ℝ))*F*(C0*profileCap r^2*Z^((919/1000:ℝ)*(1+1/1000)))*
        (2304*(8*(Z^(1/1000:ℝ)/(1/1000:ℝ)))) := by
      rw [hpow]
      gcongr
    _ = D*profileCap r^2*K*Z^((4/1000:ℝ)+(919/1000)*(1+1/1000)+1/1000) := by
      dsimp [D]
      rw [Real.rpow_add hZ0, Real.rpow_add hZ0]
      ring
    _ ≤ (D+1)*profileCap r^2*K*Z^(93/100:ℝ) := by
      have hD : 0 ≤ D := by dsimp [D,F]; positivity
      apply mul_le_mul
      · nlinarith [mul_nonneg (sq_nonneg (profileCap r)) hK]
      · exact Real.rpow_le_rpow_of_exponent_le hZ1 (by norm_num)
      · positivity
      · positivity

/-- Q uses the actual radial scale and the corresponding Poisson cutoff. -/
abbrev secondCutoffQ := QRH.Cycle092.RawSides.secondCutoffQ

/-- The second tail is summed by its actual finite seed count, retaining a
    power saving after the complete count and selected-radius factor. -/
theorem tail_terms_Q (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (ι : Type) [Fintype ι] (a b : ℝ) (r : Source ι a b) (ha : 0 < a), 0 ≤ b →
    ∀ (η₁ η₂ : Character) (V : Finset Id) (hV : ∀ v ∈ V, v ≠ 0) (ψ : Character) (t K W X : ℝ),
      1/2 ≤ K → K ≤ Z^(40:ℝ) → 1 ≤ W → W ≤ Z^(1/1000:ℝ) →
      poolCap r ≤ Z^(40:ℝ) → 0 < X → sourceNormCap r.P b r.T r.d ≤ X → X ≤ Z^(919/1000:ℝ) →
      (∀ v ∈ V, (v.absNorm : ℝ) ≤ Z^(8:ℝ)) →
      tailTerms r ha (idealCoeff η₁) (idealCoeff η₂) V ψ t (16*K*W^4) (secondCutoffQ X K W) Z ξ ≤
        C * profileCap r^2 * Z^(-22:ℝ) := by
  obtain ⟨C0,hC0,h⟩ := tail_terms_bound 40 ξ 31 (by norm_num) hξ
  refine ⟨128*C0,by positivity,h.mono ?_⟩
  intro Z hZ
  have hZ0 := zero_lt_one.trans hZ.1
  have hp (x y : ℝ) (hxy : x ≤ y) : Z^x ≤ Z^y := Real.rpow_le_rpow_of_exponent_le hZ.1.le hxy
  have hZ40 : 1 ≤ Z^(40:ℝ) := Real.one_le_rpow hZ.1.le (by norm_num)
  refine ⟨hZ.1,?_⟩
  intro ι _ a b r ha hb η₁ η₂ V hV ψ t K W X hK hKcap hW hWcap hpool hX hcap hXcap hVcap
  have hK0 : 0 < K := by linarith
  have hW0 := zero_lt_one.trans_le hW
  have hden : 1 ≤ 16*K*W^4 := by nlinarith [one_le_pow₀ hW (n:=4)]
  have hTc : secondCutoffQ X K W ≤ Z^(40:ℝ) := by
    calc
      _ ≤ X^2 := div_le_self (sq_nonneg X) hden
      _ ≤ (Z^(919/1000:ℝ))^2 := pow_le_pow_left₀ hX.le hXcap _
      _ = Z^((919/1000:ℝ)*2) := by rw [← Real.rpow_mul_natCast hZ0.le]; norm_num
      _ ≤ _ := hp _ _ (by norm_num)
  have hcount : (V.card : ℝ) ≤ 128*Z^(8:ℝ) := by
    have hs : V ⊆ idealBall (Z^(8:ℝ)) := fun v hv => (mem_idealBall _ _).mpr ⟨hV v hv,hVcap v hv⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans (idealBall_card _ (by positivity))
  have htail := hZ.2 ι a b r ha hb η₁ η₂ V ψ t K W X (secondCutoffQ X K W)
    hK0 hW0 hX hpool hcap (hXcap.trans (hp _ _ (by norm_num))) hKcap
    (hWcap.trans (hp _ _ (by norm_num)))
    ((inv_le_one_of_one_le₀ hW).trans hZ40) hTc le_rfl
  apply htail.trans
  calc
    _ ≤ (128*Z^(8:ℝ))*Z^(1/1000:ℝ)*(C0*profileCap r^2*Z^(-31:ℝ)) := by gcongr
    _ = (128*C0)*profileCap r^2*Z^((8:ℝ)+1/1000-31) := by
      rw [show (8:ℝ)+1/1000-31 = (8+1/1000)+(-31) by ring,
        Real.rpow_add hZ0,Real.rpow_add hZ0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hp _ _ (by norm_num)) (by positivity)

#print axioms zero_terms_Q
#print axioms tail_terms_Q
end
end QRH.Cycle092.RootColoredSeed
