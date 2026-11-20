/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The ordered earlier cap pair permutes whole authentic ordinary tuples. -/
import Candidate.C092.transport.StrongPairOrdinaryPrice

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.LowActual
local notation "O" => ActualEisensteinCubic.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
variable (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)

theorem pairAt_swap {N Y l bΦ mesh ε Z C : ℝ} {W : ℝ→ℂ}
    {η₁ η₂ η₀₁ η₀₂ : Character} {Q₁ Q₂ : Ideal O} {degree : ℕ} {controls : Finset (ℕ×ℕ)}
    (hsrc : PairAt (Slot:=Slot) rayM Hr hHr N Y l W bΦ mesh ε Z
      η₁ η₂ η₀₁ η₀₂ Q₁ Q₂ degree controls C) :
    PairAt (Slot:=Slot) rayM Hr hHr Y N l W bΦ mesh ε Z
      η₂ η₁ η₀₂ η₀₁ Q₂ Q₁ degree controls C := by
  intro T θ₁ θ₂ w σ₁ σ₂ v₁ v₂ t₁ t₂ height hw hwm hlo₁ hhi₁ hlo₂ hhi₂ hh hv₁ hv₂ hsum
    p X₁ X₂ hX₁ hX₂ hXN hXY s mark hk₁ hk₂ hy hm₁ hm₂
  let p' : Profiles (1/4) (9/4) :=
    ⟨fun i=>if i=0 then p.profile 1 else p.profile 0,fun i=>by split_ifs <;> exact p.support _⟩
  have hp : p'.control controls=p.control controls := by
    simp only [p',Profiles.control,ite_true,show (1:Fin 2)≠0 from by decide,ite_false]
    ring
  have h := hsrc T θ₂ θ₁ w σ₂ σ₁ v₂ v₁ t₂ t₁ height hw hwm hlo₂ hhi₂ hlo₁ hhi₁ hh hv₂ hv₁
    hsum p' X₂ X₁ hX₂ hX₁ hXY hXN s mark hk₂ hk₁ hy hm₂ hm₁
  rw [hp] at h
  simp only [p',ite_true,show (1:Fin 2)≠0 from by decide,ite_false] at h
  rw [finiteEnergyOn_swap] at h
  have hhgt : 1+|t₂|+|t₁|+height=1+|t₁|+|t₂|+height := by ring
  simpa only [hhgt] using h

theorem pairUnit_swap {N Y l mesh ε : ℝ} (hsrc : PairUnitBox N Y l mesh ε) :
    PairUnitBox Y N l mesh ε := by
  intro Slot _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ hΦs η₁ η₂ η₀₁ η₀₂ Q₁ Q₂
    hQ₁ray hQ₁0 hQ₁top hQ₁72 hQ₂ray hQ₂0 hQ₂top hQ₂72
  obtain ⟨d,S,C,hC,h⟩ := hsrc Slot rayM Hr hHr W hW hWs bΦ hbΦ hΦs η₂ η₁ η₀₂ η₀₁ Q₂ Q₁
    hQ₂ray hQ₂0 hQ₂top hQ₂72 hQ₁ray hQ₁0 hQ₁top hQ₁72
  exact ⟨d,S,C,hC,h.mono (fun _ h=>pairAt_swap rayM Hr hHr h)⟩

theorem pairUniform_swap {N Y l : ℝ} (hsrc : PairUniformBox N Y l) : PairUniformBox Y N l := by
  intro ε hε
  obtain ⟨mesh,hm,h⟩ := hsrc ε hε
  exact ⟨mesh,hm,pairUnit_swap h⟩

/-- The full genuine earlier cover supplies the unordered physical pair,
with its source gain taken conservatively at the larger witness cap. -/
theorem ordinary_earlier_pair {n y m l : ℝ} (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hm0 : y/(H:ℝ) ≤ m) (hm1 : m ≤ sourceY)
    (hl0 : 0 ≤ l) (hl : l < frozenCapacity n m) :
    PairUniformBox (n/(H:ℝ)) m l := by
  have hAdj := adjustedWitness_at_H hn1 hm0
  have hseam : adjustedWitness n m (H:ℝ) ≤ sourceY := by simpa only [hAdj] using hm1
  have hprior := earlier_adjusted_pair cover hy0 hn0 hn1 hm0 H_real_bounds.1 le_rfl hseam
  rw [hAdj] at hprior
  have hgain := sourceGain_antitone (min_le_right (n/(H:ℝ)) m) hm1
  have hsum : max (n/(H:ℝ)) m+min (n/(H:ℝ)) m=n/(H:ℝ)+m := max_add_min _ _
  have hquota : frozenCapacity n m ≤ sourceWidth (max (n/(H:ℝ)) m) (min (n/(H:ℝ)) m) := by
    unfold frozenCapacity sourceWidth
    rw [continuedGain,ite_eq_left hm1]
    linarith
  have hsrc := hprior l hl0 (hl.trans_le hquota)
  by_cases hnm : m ≤ n/(H:ℝ)
  · simpa only [max_eq_left hnm,min_eq_right hnm] using hsrc
  · have hnm' := (le_of_not_ge hnm)
    apply pairUniform_swap
    simpa only [max_eq_right hnm',min_eq_left hnm'] using hsrc

#print axioms pairAt_swap
#print axioms ordinary_earlier_pair
end
end QRH.Cycle092.StrongPair
