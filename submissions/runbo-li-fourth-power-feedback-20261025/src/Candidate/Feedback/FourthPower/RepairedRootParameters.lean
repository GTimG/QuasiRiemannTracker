/- Copyright (c) 2026 Sil. Apache-2.0.
Root-centering parameters. Mesh precedes N, losses follow the positive
N-dependent gain.
-/
import Candidate.Feedback.FourthPower.MixedFirstUniformLossBudget
import Candidate.Feedback.FourthPower.IncumbentInput

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.RepairedRootParameters
noncomputable section
open OAI.SevenEighths MixedFirstUniformLossBudget

def rootReserve : ℝ := 1/100000
def mesh (ε:ℝ) : ℝ := min (rootReserve/1024) (ε/1024)
def widthFloor (ε:ℝ) : ℝ := mesh ε
def mixedReserve : ℝ := rootReserve/8
def omegaLoss (ε:ℝ) : ℝ := min (rootReserve/100000) (ε/100000)
def windowLoss (ε:ℝ) : ℝ := min 1 ε/100
def windowCap (N:ℕ)(ε:ℝ) : ℝ := 8+(N:ℝ)*mesh ε
def seedCap (N:ℕ)(ε:ℝ) : ℝ := 7+(N:ℝ)*mesh ε
def stepN (N:ℕ)(ε:ℝ) : ℝ :=
  budgetStep (windowCap N ε) (seedCap N ε) (windowLoss ε) mixedReserve
def internalScale (N:ℕ)(ε:ℝ) : ℝ :=
  min (stepN N ε) (min (omegaLoss ε) (widthFloor ε/400))
def cutoffLoss (N:ℕ)(ε:ℝ) : ℝ := internalScale N ε/1000
def artificialLoss (N:ℕ)(ε:ℝ) : ℝ := internalScale N ε/1000
def massLoss (N:ℕ)(ε:ℝ) : ℝ := internalScale N ε/1000
def commonPower (N:ℕ)(ε:ℝ) : ℝ := internalScale N ε/(1000*(seedCap N ε+1))

theorem mesh_spec (ε:ℝ)(hε:0<ε) :
    0<mesh ε ∧ mesh ε≤rootReserve/1024 ∧ mesh ε≤ε/1024 := by
  exact ⟨lt_min (by norm_num [rootReserve]) (by positivity),min_le_left _ _,min_le_right _ _⟩

theorem omega_spec (ε:ℝ)(hε:0<ε) :
    0<omegaLoss ε ∧ omegaLoss ε≤rootReserve/100000 ∧
      omegaLoss ε≤ε/100000 ∧ omegaLoss ε≤1/10000000000 := by
  refine ⟨lt_min (by norm_num [rootReserve]) (by positivity),min_le_left _ _,min_le_right _ _,?_⟩
  exact (min_le_left _ _).trans (by norm_num [rootReserve])

theorem cap_spec (N:ℕ)(ε:ℝ)(hε:0<ε) :
    1≤windowCap N ε ∧ 0≤seedCap N ε ∧ 0<windowLoss ε ∧ 0<mixedReserve := by
  have hprod:=mul_nonneg (Nat.cast_nonneg N) (mesh_spec ε hε).1.le
  refine ⟨?_,?_,div_pos (lt_min zero_lt_one hε) (by norm_num),by norm_num [mixedReserve,rootReserve]⟩
  · dsimp only [windowCap];linarith
  · dsimp only [seedCap];linarith

theorem step_pos (N:ℕ)(ε:ℝ)(hε:0<ε) : 0<stepN N ε := by
  have h:=cap_spec N ε hε
  exact budget_step_pos _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem internal_spec (N:ℕ)(ε:ℝ)(hε:0<ε) :
    0 < internalScale N ε ∧ internalScale N ε≤stepN N ε ∧
      internalScale N ε≤omegaLoss ε ∧ internalScale N ε≤widthFloor ε/400 := by
  refine ⟨lt_min (step_pos N ε hε) (lt_min (omega_spec ε hε).1 (by
    exact div_pos (mesh_spec ε hε).1 (by norm_num))),min_le_left _ _,?_,?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- The combined error fits the actual N-dependent gain; no reverse
comparison between the source mesh and that gain is assumed. -/
theorem internal_losses_paid (N:ℕ)(ε:ℝ)(hε:0<ε) :
    0<cutoffLoss N ε ∧ 0<artificialLoss N ε ∧ 0<massLoss N ε ∧ 0<commonPower N ε ∧
    4*cutoffLoss N ε+artificialLoss N ε+2*seedCap N ε*commonPower N ε+massLoss N ε≤
      min (stepN N ε/4) (min (omegaLoss ε/4) ((widthFloor ε/400)/4)) := by
  have hs:=internal_spec N ε hε
  have hs0 : 0 < internalScale N ε := hs.1
  have hB:0≤seedCap N ε:=(cap_spec N ε hε).2.1
  have hp:0<commonPower N ε:=by unfold commonPower;positivity
  have he:commonPower N ε*(1000*(seedCap N ε+1))=internalScale N ε:=by
    unfold commonPower
    exact div_mul_cancel₀ _ (by positivity)
  have hc:2*seedCap N ε*commonPower N ε ≤ internalScale N ε/500:=by nlinarith
  refine ⟨by unfold cutoffLoss;positivity,by unfold artificialLoss;positivity,
    by unfold massLoss;positivity,hp,?_⟩
  apply le_min
  · dsimp only [cutoffLoss,artificialLoss,massLoss];linarith [hs.2.1]
  · apply le_min
    · dsimp only [cutoffLoss,artificialLoss,massLoss];linarith [hs.2.2.1]
    · dsimp only [cutoffLoss,artificialLoss,massLoss];linarith [hs.2.2.2]

theorem original_reserve_paid (N:ℕ)(ε:ℝ)(hε:0<ε) :
    mixedReserve+4*mesh ε+4*cutoffLoss N ε≤rootReserve := by
  have hm:mesh ε≤rootReserve/1024:=(mesh_spec ε hε).2.1
  have ho:omegaLoss ε≤rootReserve/100000:=(omega_spec ε hε).2.1
  have hs:internalScale N ε≤omegaLoss ε:=(internal_spec N ε hε).2.2.1
  dsimp only [mixedReserve,cutoffLoss]
  norm_num [rootReserve] at hm ho ⊢
  linarith

def Face (P S:ℝ) : Prop := 0≤S ∧ S≤3/50 ∧ P+(93/25)*S≤1-rootReserve
def lower (P S:ℝ) : ℝ := (3/2)*(P+S-5/6)
def upperOne (P S:ℝ) : ℝ := (P-S-1/2)/2
def upperTwo (S:ℝ) : ℝ := 3/10-S
def NeedsCentering (ε P S:ℝ) : Prop := 5/6-10*omegaLoss ε<P+S
def centeredLower (ε P S:ℝ) : ℝ := max 0 (lower P S)+20*omegaLoss ε
def centeredUpper (ε P S:ℝ) : ℝ := min (upperOne P S) (upperTwo S)-20*omegaLoss ε
def centeredExponent (ε P S:ℝ) : ℝ := (centeredLower ε P S+centeredUpper ε P S)/2

theorem face_volume {P S:ℝ}(h:Face P S) : P+S≤1-rootReserve := by
  rcases h with ⟨hS,hcap,hface⟩
  linarith

theorem upper_order {P S:ℝ}(h:Face P S) : upperOne P S<upperTwo S := by
  have hv:=face_volume h
  dsimp only [upperOne,upperTwo]
  norm_num [rootReserve] at hv
  linarith

theorem interval_gap {P S:ℝ}(h:Face P S) :
    rootReserve+(43/25)*S≤upperOne P S-lower P S ∧
      1/20+(3/2)*rootReserve+(77/25)*S≤upperTwo S-lower P S := by
  rcases h with ⟨hS,hcap,hface⟩
  dsimp only [upperOne,upperTwo,lower]
  constructor <;> linarith

theorem centering_interval {ε P S:ℝ}(hε:0<ε)(h:Face P S)
    (hhigh:NeedsCentering ε P S) : centeredLower ε P S<centeredUpper ε P S := by
  have ho:=omega_spec ε hε
  have hg:=interval_gap h
  have hu:=upper_order h
  have hS:=h.1
  have hcap:=h.2.1
  unfold centeredLower centeredUpper
  rw [min_eq_left hu.le]
  by_cases hl:0≤lower P S
  · rw [max_eq_right hl]
    have hω:omegaLoss ε≤rootReserve/100000:=ho.2.1
    have hgap:=hg.1
    norm_num [rootReserve] at hω hgap
    linarith
  · rw [max_eq_left (le_of_not_ge hl)]
    have hnear:8/75-5*omegaLoss ε<upperOne P S := by
      dsimp only [NeedsCentering] at hhigh
      dsimp only [upperOne]
      linarith
    have hω:omegaLoss ε≤1/10000000000:=ho.2.2.2
    linarith

/-- The root exponent is fixed before every first common label or
genuine allocation and is unrelated to a later selected-width choice. -/
theorem centered_spec {ε P S:ℝ}(hε:0<ε)(h:Face P S)(hhigh:NeedsCentering ε P S) :
    0<centeredExponent ε P S ∧ centeredExponent ε P S<P/2 ∧
      lower P S+20*omegaLoss ε<centeredExponent ε P S ∧
      centeredExponent ε P S<upperOne P S-20*omegaLoss ε ∧
      centeredExponent ε P S<upperTwo S-20*omegaLoss ε ∧
      centeredExponent ε P S<1 := by
  have hi:=centering_interval hε h hhigh
  have ho:0<omegaLoss ε:=(omega_spec ε hε).1
  have hl:centeredLower ε P S<centeredExponent ε P S:=by unfold centeredExponent;linarith
  have hu:centeredExponent ε P S<centeredUpper ε P S:=by unfold centeredExponent;linarith
  have hl0:0≤max 0 (lower P S):=le_max_left _ _
  have hll:lower P S≤max 0 (lower P S):=le_max_right _ _
  have hu1:centeredExponent ε P S<upperOne P S-20*omegaLoss ε:=
    hu.trans_le (sub_le_sub_right (min_le_left _ _) _)
  have hu2:centeredExponent ε P S<upperTwo S-20*omegaLoss ε:=
    hu.trans_le (sub_le_sub_right (min_le_right _ _) _)
  have hS:=h.1
  refine ⟨?_,?_,?_,hu1,hu2,?_⟩
  · dsimp only [centeredLower] at hl;linarith
  · dsimp only [upperOne] at hu1;linarith
  · dsimp only [centeredLower] at hl;linarith
  · dsimp only [upperTwo] at hu2;linarith

theorem centered_exceptional_margin {ε P S:ℝ}(hε:0<ε)(h:Face P S)
    (hhigh:NeedsCentering ε P S) :
    P+S-5/6-(2/3)*centeredExponent ε P S≤-10*omegaLoss ε := by
  have hs:lower P S+20*omegaLoss ε<centeredExponent ε P S:=
    (centered_spec hε h hhigh).2.2.1
  have ho:0<omegaLoss ε:=(omega_spec ε hε).1
  dsimp only [lower] at hs
  linarith

theorem low_exceptional_margin {ε P S:ℝ}(h:¬NeedsCentering ε P S) :
    P+S-5/6≤-10*omegaLoss ε := by
  have he: P+S≤5/6-10*omegaLoss ε:=le_of_not_gt h
  linarith

/-- Actual reference provider inputs R=1+omega,d=omega,deltaRef=omega
and xiRef=omega. All fixed-factor and small-loss gates are displayed. -/
theorem reference_gates {ε P S:ℝ}(hε:0<ε)(h:Face P S)(hhigh:NeedsCentering ε P S) :
    P+2*S+4*omegaLoss ε<1+omegaLoss ε ∧
      centeredExponent ε P S+((1+omegaLoss ε)+omegaLoss ε)/2+S+2*omegaLoss ε≤
        (4/5)*(1+omegaLoss ε) ∧
      (1+omegaLoss ε)+omegaLoss ε+2*centeredExponent ε P S-P+S+2*omegaLoss ε≤
        (1+omegaLoss ε)/2 ∧ omegaLoss ε/2≤omegaLoss ε := by
  have hs:=centered_spec hε h hhigh
  have ho:=omega_spec ε hε
  have hface:=h.2.2
  have hS:=h.1
  have hu1:=hs.2.2.2.1
  have hu2:=hs.2.2.2.2.1
  refine ⟨?_,?_,?_,by linarith [ho.1]⟩
  · have hω:=ho.2.1
    norm_num [rootReserve] at hface hω
    linarith
  · dsimp only [upperTwo] at hu2;linarith [ho.1]
  · dsimp only [upperOne] at hu1;linarith [ho.1]

theorem contrary_inputs (hcontra:theta<HeckeZeroSupremum.beta) :
    (51/100:ℝ)≤HeckeZeroSupremum.beta ∧ 2*HeckeZeroSupremum.beta-1≤(3/4:ℝ) :=
  IncumbentInput.contrary_inputs hcontra

end
end Candidate.Feedback.FourthPower.RepairedRootParameters
