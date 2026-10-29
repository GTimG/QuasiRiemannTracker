/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Domain-containment transport for the literal source interface.
The source contraction below is adapted from Hailey Collet's
Record12518109Source.InitialMoment (Apache-2.0); inherited source is unchanged. -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.SourceInlet
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource
set_option autoImplicit false
namespace Qrh.JointDetector.RestartSourceDomain
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot
open QRH.Record12518109Source QRH.Record12518109Existence Filter
local notation "O" => HeckeFamily.O

def Contains (strong weak : SourceFace) : Prop :=
 ∀ {m₁ m₂ s M : ℝ}, 0 ≤ M → weak.Admissible m₁ m₂ s M →
 strong.Admissible m₁ m₂ s M

theorem contains_of_affine {strong weak : SourceFace}
 (hplo : strong.plainLo ≤ weak.plainLo)
 (hphi : weak.plainHi ≤ strong.plainHi)
 (hslo : strong.slotLo ≤ weak.slotLo)
 (hshi : weak.slotHi ≤ strong.slotHi)
 (hs0 : 0 ≤ weak.slotLo)
 (hbudget : weak.B + max (strong.lam-weak.lam) 0 * weak.slotHi ≤ strong.B) :
 Contains strong weak := by
 intro m₁ m₂ s M hM ha
 rcases ha with ⟨h₁lo,h₁hi,h₂lo,h₂hi,hslotlo,hslothi,hb⟩
 refine ⟨(mul_le_mul_of_nonneg_right hplo hM).trans h₁lo,
   h₁hi.trans (mul_le_mul_of_nonneg_right hphi hM),
   (mul_le_mul_of_nonneg_right hplo hM).trans h₂lo,
   h₂hi.trans (mul_le_mul_of_nonneg_right hphi hM),
   (mul_le_mul_of_nonneg_right hslo hM).trans hslotlo,
   hslothi.trans (mul_le_mul_of_nonneg_right hshi hM), ?_⟩
 have hs : 0 ≤ s := (mul_nonneg hs0 hM).trans hslotlo
 have hg0 : 0 ≤ max (strong.lam-weak.lam) 0 := le_max_right _ _
 have hg : (strong.lam-weak.lam)*s ≤ max (strong.lam-weak.lam) 0*weak.slotHi*M := calc
  _ ≤ max (strong.lam-weak.lam) 0*s :=
   mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  _ ≤ max (strong.lam-weak.lam) 0*(weak.slotHi*M) :=
   mul_le_mul_of_nonneg_left hslothi hg0
  _ = _ := by ring
 have hBM := mul_le_mul_of_nonneg_right hbudget hM
 nlinarith

/-- Exact affine-domain transport permits a slope decrease when the intercept
pays its full cost at the target cap. -/
theorem global_contains_global {B₀ L₀ c₀ B L c : ℝ}
 (hc : 0 ≤ c) (hcap : c ≤ c₀)
 (hbudget : B + max (L₀-L) 0*c ≤ B₀) :
 Contains (QRH.Record1252270103Return.globalFace B₀ L₀ c₀)
   (QRH.Record1252270103Return.globalFace B L c) := by
 have hB : B ≤ B₀ := by
   have hh := mul_nonneg (le_max_right (L₀-L) 0) hc
   linarith
 apply contains_of_affine <;>
   simp only [QRH.Record1252270103Return.globalFace]
 · exact le_rfl
 · exact hB
 · exact le_rfl
 · exact hcap
 · exact le_rfl
 · exact hbudget

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ H)
theorem initialAffineAt_of_contains {strong weak : SourceFace}
    (hface : Contains strong weak) (W : ℝ → ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ)
    (hMmin : 0 ≤ Mmin)
    (hsource : InitialAffineAt (α:=α) rayModulus H hH strong W
      bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree S C) :
    InitialAffineAt (α:=α) rayModulus H hH weak W
      bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hadm
  exact hsource T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂
    (hface (hMmin.trans hMlo) hadm)


omit [Fintype α] [DecidableEq α] in
 theorem unit_source_of_contains {strong weak : SourceFace} (hface : Contains strong weak)
    {mesh ε : ℝ} (hsource : UnitFaceSource strong mesh ε) : UnitFaceSource weak mesh ε := by
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,S,C,hC,hsource⟩ := hsource α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  exact ⟨degree,S,C,hC,hsource.mono (fun Z hZ=>initialAffineAt_of_contains rayM H hH hface W
    2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q degree S C (by norm_num) hZ)⟩

/-- Uniformity is unchanged: the finite source choice precedes every mesh and
moving arithmetic datum. -/
theorem uniform_source_of_contains {strong weak : SourceFace}
 (hface : Contains strong weak) (hsource : UniformUnitFaceSource strong) :
 UniformUnitFaceSource weak := by
 intro ε hε
 obtain ⟨mesh, hm, hs⟩ := hsource ε hε
 exact ⟨mesh, hm, unit_source_of_contains hface hs⟩

end
end Qrh.JointDetector.RestartSourceDomain
