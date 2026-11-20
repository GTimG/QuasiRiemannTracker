/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform homogeneous profile controls for the genuine fixed-row H8 source.
The lattice, source-control and Euler-convolution inputs retain their original
OpenAI/Collet and other notices through the imported source modules. -/
import Candidate.C092.transport.FixedCubeApplication
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace QRH.Cycle092.SignedCenter
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => HeckeFamily.O

def h8Profile (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    {a b : ℝ} (ha : 0<a) (hb : 0≤b) (W : 𝓢(ℝ,ℂ))
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b) : OrdinaryProfile where
  W := W
  a := a
  b := b
  M := sourceControl S W
  t := 0
  ha := ha
  hb := hb
  hM := sourceControl_nonneg S W
  hs := hs
  hW := W.smooth ⊤
  hbound := fun y => (SchwartzMap.norm_le_seminorm ℝ W y).trans
    (Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS)

def h8UnitProfile (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    {a b : ℝ} (ha : 0<a) (hb : 0≤b) (W : 𝓢(ℝ,ℂ))
    (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b) : OrdinaryProfile where
  W := normalizedProfile S W
  a := a
  b := b
  M := 1
  t := 0
  ha := ha
  hb := hb
  hM := zero_le_one
  hs := (normalizedProfile_support S W).trans hs
  hW := (normalizedProfile S W).smooth ⊤
  hbound := fun y => (SchwartzMap.norm_le_seminorm ℝ (normalizedProfile S W) y).trans
    ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans
      (normalizedProfile_control S W))

/-- One degree and finite seminorm set precede both live profiles. Constants
are obtained from the authentic uniform lattice-volume control, not from a
choice of constants separately for each normalized profile. -/
theorem h8_unit_pairK (a b ε B : ℝ) (ha : 0<a) (hb : 0≤b)
    (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ hS : (0,0)∈S,
    ∀ Q₁ Q₂ : Ideal O, ∃ C : ℝ, 0<C ∧
    ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
    ∀ hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Icc a b,
    ∀ hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Icc a b,
    ∀ (R₁ R₂ : OrdinaryRow), R₁.Q=Q₁ → R₂.Q=Q₂ →
    ∀ U : ℝ, 1≤U → (Ideal.absNorm R₁.χ.modulus:ℝ)≤U^B →
      (Ideal.absNorm R₂.χ.modulus:ℝ)≤U^B → ∀ t₁ t₂ : ℝ,
    pairK R₁ R₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁)
      ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂) ≤
      C*U^ε*(1+‖t₁‖+‖t₂‖)^J := by
  obtain ⟨J,S,hS,hvol⟩ := volumeControl_source_control a b ε B ha hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q₁ Q₂
  obtain ⟨D₁,hD₁,h₁⟩ := hvol Q₁
  obtain ⟨D₂,hD₂,h₂⟩ := hvol Q₂
  let V : ℝ := 128*(b+b)
  have hV : 0≤V := by dsimp [V]; positivity
  refine ⟨1+2*V^2+4*(D₁+D₂)*V,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ R₁ R₂ hQ₁ hQ₂ U hU hn₁ hn₂ t₁ t₂
  let H : ℝ := 1+‖t₁‖+‖t₂‖
  let A : ℝ := U^ε*H^J
  have hH : 1≤H := by change 1≤1+‖t₁‖+‖t₂‖; linarith [norm_nonneg t₁,norm_nonneg t₂]
  have hA : 1≤A := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hU hε.le) (one_le_pow₀ hH)
  have hp₁ : (1+‖t₁‖)^J≤H^J := by apply pow_le_pow_left₀ (by positivity); change 1+‖t₁‖≤1+‖t₁‖+‖t₂‖; linarith [norm_nonneg t₂]
  have hp₂ : (1+‖t₂‖)^J≤H^J := by apply pow_le_pow_left₀ (by positivity); change 1+‖t₂‖≤1+‖t₁‖+‖t₂‖; linarith [norm_nonneg t₁]
  have bound (Q : Ideal O) (D : ℝ) (hD : 0<D)
      (hv : ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b,
        ∀ U : ℝ, 1≤U → ∀ χ : Character, (Ideal.absNorm χ.modulus:ℝ)≤U^B → ∀ t : ℝ,
        volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
          D*sourceControl S W*U^ε*(1+‖t‖)^J)
      (W : 𝓢(ℝ,ℂ)) (hs : Function.support (W:ℝ→ℂ) ⊆ Set.Icc a b)
      (χ : Character) (hn : (Ideal.absNorm χ.modulus:ℝ)≤U^B) (t : ℝ)
      (hp : (1+‖t‖)^J≤H^J) :
      volumeControl Q χ ((h8UnitProfile S hS ha hb W hs).atHeight t).normalized ≤ D*A := by
    have h := hv (normalizedProfile S W) ((normalizedProfile_support S W).trans hs) U hU χ hn t
    apply h.trans
    dsimp only [A]
    calc
      _ ≤ D*1*U^ε*H^J := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (normalizedProfile_control S W) hD.le) (by positivity)
        · exact hp
        · positivity
        · positivity
      _ = _ := by ring
  have he₁ := bound Q₁ D₁ hD₁ h₁ W₁ hs₁ R₁.χ hn₁ t₁ hp₁
  have he₂ := bound Q₂ D₂ hD₂ h₂ W₂ hs₂ R₂.χ hn₂ t₂ hp₂
  have hE : pairE R₁ R₂ ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁)
      ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂) ≤ (D₁+D₂)*A := by
    dsimp only [pairE]
    rw [hQ₁,hQ₂]
    linarith
  have hc : pairC ((h8UnitProfile S hS ha hb W₁ hs₁).atHeight t₁)
      ((h8UnitProfile S hS ha hb W₂ hs₂).atHeight t₂)=V := by simp [pairC,h8UnitProfile,OrdinaryProfile.atHeight,V]
  unfold pairK
  rw [hc]
  rw [mul_assoc (1+2*V^2+4*(D₁+D₂)*V)]
  change 2*V^2+4*_ *V ≤ (1+2*V^2+4*(D₁+D₂)*V)*A
  have hm := mul_le_mul_of_nonneg_right hE (by positivity : 0≤4*V)
  have hs := mul_le_mul_of_nonneg_left hA (by positivity : 0≤2*V^2)
  nlinarith

#print axioms h8_unit_pairK
end
end QRH.Cycle092.SignedCenter
