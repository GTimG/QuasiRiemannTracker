/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Common early mesh for a genuine finite preceding-source bank. -/
import Candidate.C092.transport.LowActualOrderedCover

set_option autoImplicit false
namespace QRH.Cycle092.LowActual
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open QRH.Cycle092.NativeStrip
open HeckeFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

/-- Narrowing the early mesh only restricts the original live arrays. -/
theorem labelledAt_mono_mesh {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    {N Y l bslot a b bΦ small large σlo σhi Mmin Mmax ε U C : ℝ}
    {W : ℝ → ℂ} {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hmesh : small ≤ large)
    (hsrc : LabelledAt (α := Slot) rayM Hr hHr N Y l W bslot a b bΦ large
      σlo σhi Mmin Mmax ε U η η₀ Q degree controls C) :
    LabelledAt (α := Slot) rayM Hr hHr N Y l W bslot a b bΦ small
      σlo σhi Mmin Mmax ε U η η₀ Q degree controls C := by
  intro T θ w σ v t height hw hwm hlo hhi hh hv M hM hM' Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hbox
  exact hsrc T θ w σ v t height hw (fun j => (hwm j).trans hmesh) hlo hhi hh hv
    M hM hM' Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hbox

theorem unitBox_mono_mesh {N Y l small large ε : ℝ}
    (hmesh : small ≤ large) (hsrc : UnitBox N Y l large ε) : UnitBox N Y l small ε := by
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,C,hC,hU⟩ := hsrc Slot rayM Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  exact ⟨degree,controls,C,hC,hU.mono (fun _ h => labelledAt_mono_mesh rayM Hr hHr hmesh h)⟩

/-- Each genuine finite cap bank admits a single positive mesh before all
arithmetic metadata. This takes no compactness or uniformity for granted. -/
theorem finite_bank_mesh {Index : Type*} [DecidableEq Index]
    (bank : Finset Index) (N Y l : Index → ℝ)
    (hsources : ∀ i ∈ bank, UniformBox (N i) (Y i) (l i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ i ∈ bank, UnitBox (N i) (Y i) (l i) mesh ε := by
  induction bank using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | insert i bank hi ih =>
    obtain ⟨a,ha,hsource⟩ := hsources i (Finset.mem_insert_self _ _) ε hε
    obtain ⟨b,hb,hbank⟩ := ih (fun j hj => hsources j (Finset.mem_insert_of_mem hj))
    refine ⟨min a b,lt_min ha hb,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact unitBox_mono_mesh (min_le_left _ _) hsource
    · exact unitBox_mono_mesh (min_le_right _ _) (hbank j hj)

/-- Instantiation for finite previous-stage P.2 pairs and their real strict
width decrements. The prefix and every decrement remain explicit. -/
theorem earlier_finite_bank {Index : Type*} [DecidableEq Index]
    {y : ℝ} (cover : EarlierCover OpenWidth y) (bank : Finset Index)
    (N Y l : Index → ℝ)
    (hprior : ∀ i ∈ bank, y/(QRH.SourceCertificate.H : ℝ) ≤ Y i)
    (htop : ∀ i ∈ bank, Y i ≤ QRH.Cycle090.sourceY/(QRH.SourceCertificate.H : ℝ))
    (hord : ∀ i ∈ bank, Y i ≤ N i)
    (hratio : ∀ i ∈ bank, N i ≤ QRH.Cycle090.sourceRatio*Y i)
    (hl0 : ∀ i ∈ bank, 0 ≤ l i)
    (hl : ∀ i ∈ bank, l i < QRH.Cycle090.sourceWidth (N i) (Y i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ i ∈ bank, UnitBox (N i) (Y i) (l i) mesh ε := by
  apply finite_bank_mesh bank N Y l _ hε
  intro i hi
  exact cover (N i) (Y i) (hprior i hi) (htop i hi) (hord i hi) (hratio i hi)
    (l i) (hl0 i hi) (hl i hi)

end
end QRH.Cycle092.LowActual
