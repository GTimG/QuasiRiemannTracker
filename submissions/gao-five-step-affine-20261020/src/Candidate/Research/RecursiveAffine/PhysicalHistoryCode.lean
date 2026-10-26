/- The actual physical second-block dictionary key. Apache-2.0; native PR67 source encodings retained.
The actual source index is copied as a definitional alias, avoiding unrelated producer imports. -/
import Candidate.Research.RecursiveAffine.DecoratedHistory
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondEnergySplit
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentActiveSource
open CenteredMomentCanonicalFirst CenteredMomentSecondBlockAggregate
open CenteredMomentSecondLiveBlock CenteredMomentSecondLocalization
open CenteredMomentSecondEnergySplit CenteredMomentSecondActivePhysicalDictionary
open CenteredMomentHeckeColumnWindow
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O
local instance physicalHistoryDecidableSum {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- Definitionally the native ActualSecondBlockIndex; no new model source is introduced. -/
abbrev ActualSecondBlockIndex {ι : Type*} [Fintype ι]
    (s : Input ι) (R seed : Ideal O) (K Tsec Z ξ : ℝ) :=
  (p : liveLabels s.η (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed)) ×
    (U : Finset (CommonIndex p.val.val.1 p.val.val.2)) ×
      SourceBlocks p.val.val.1 p.val.val.2 U K (frequencyRadius Tsec Z ξ) (sourceRadius s)

abbrev SecondArithmeticLabel := (CD : Ideal O × Ideal O) × Finset (CommonIndex CD.1 CD.2)

def actualSecondArithmeticLabel {ι : Type*} [Fintype ι] (s : Input ι)
    (R seed : Ideal O) (K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) : SecondArithmeticLabel :=
  ⟨q.1.val.val,q.2.1⟩

def actualSecondDyad {ι : Type*} [Fintype ι] (s : Input ι)
    (R seed : Ideal O) (K Tsec Z ξ : ℝ)
    (q : ActualSecondBlockIndex s R seed K Tsec Z ξ) : Fin 4 → ℤ := fun i => (q.2.2 i : ℤ)

theorem actual_second_label_dyad_injective {ι : Type*} [Fintype ι] (s : Input ι)
    (R seed : Ideal O) (K Tsec Z ξ : ℝ) :
    Function.Injective (fun q : ActualSecondBlockIndex s R seed K Tsec Z ξ =>
      (actualSecondArithmeticLabel s R seed K Tsec Z ξ q, actualSecondDyad s R seed K Tsec Z ξ q)) := by
  rintro ⟨p,U,n⟩ ⟨p',U',n'⟩ h
  have hp : p.val.val = p'.val.val := congrArg (fun x : SecondArithmeticLabel × (Fin 4 → ℤ) => x.1.1) h
  have hp' : p = p' := Subtype.ext (Subtype.ext hp)
  cases hp'
  have hlabel := congrArg Prod.fst h
  have hU : U = U' := eq_of_heq (Sigma.mk.inj_iff.mp hlabel).2
  cases hU
  have hn := congrArg Prod.snd h
  have hn' : n = n' := funext (fun i => Subtype.ext (congrFun hn i))
  cases hn'
  rfl

/-- The literal source key includes the old seed and all four dyad coordinates.
The selected residual ideal and its allocation are deterministic metadata of this key,
never extra free coordinates in the prefix count. -/
def physicalHistoryCode {α : Type*} [Fintype α] [DecidableEq α] {Label : Type*}
    (slots : Label → Finset α) (s : (l : Label) → Input (slots l))
    (R seed : Label → Ideal O) (K Tsec : Label → ℝ) (Z ξ : ℝ)
    (first : Label → FirstSourceLabel)
    (r : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ) : DecoratedPrefix :=
  (⟨first r.1, actualSecondArithmeticLabel (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2⟩,
    seed r.1, actualSecondDyad (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ r.2)

/-- The source's existing first-label/seed injection and native label/dyad injection
produce the complete history injection. Bare ChildPrefix alone is not injective. -/
theorem physicalHistoryCode_injective {α : Type*} [Fintype α] [DecidableEq α] {Label : Type*}
    (slots : Label → Finset α) (s : (l : Label) → Input (slots l))
    (R seed : Label → Ideal O) (K Tsec : Label → ℝ) (Z ξ : ℝ)
    (first : Label → FirstSourceLabel) (hfirst : Function.Injective (fun l => (first l, seed l))) :
    Function.Injective (physicalHistoryCode slots s R seed K Tsec Z ξ first) := by
  rintro ⟨l,q⟩ ⟨l',q'⟩ h
  have hf : first l = first l' := congrArg (fun x : DecoratedPrefix => x.1.1) h
  have hs : seed l = seed l' := congrArg (fun x : DecoratedPrefix => x.2.1) h
  have hl : l = l' := hfirst (Prod.ext hf hs)
  subst l'
  have ha : actualSecondArithmeticLabel (s l) (R l) (seed l) (K l) (Tsec l) Z ξ q =
      actualSecondArithmeticLabel (s l) (R l) (seed l) (K l) (Tsec l) Z ξ q' :=
    congrArg (fun x : DecoratedPrefix => x.1.2) h
  have hd : actualSecondDyad (s l) (R l) (seed l) (K l) (Tsec l) Z ξ q =
      actualSecondDyad (s l) (R l) (seed l) (K l) (Tsec l) Z ξ q' :=
    congrArg (fun x : DecoratedPrefix => x.2.2) h
  have hq := actual_second_label_dyad_injective (s l) (R l) (seed l) (K l) (Tsec l) Z ξ (Prod.ext ha hd)
  exact Sigma.ext rfl (heq_of_eq hq)

/-- The recorded seed is a squarefree divisor of the actual second-common C;
these are exactly the gate facts used by the native rows-per-prefix count. -/
theorem physicalHistoryCode_seed {α : Type*} [Fintype α] [DecidableEq α] {Label : Type*}
    (slots : Label → Finset α) (s : (l : Label) → Input (slots l))
    (R seed : Label → Ideal O) (hseed : ∀ l, Squarefree (seed l))
    (hz₁ : ∀ l, (s l).W₁ 0 = 0) (hz₂ : ∀ l, (s l).W₂ 0 = 0)
    (K Tsec : Label → ℝ) (Z ξ : ℝ) (first : Label → FirstSourceLabel)
    (r : (l : Label) × ActualSecondBlockIndex (s l) (R l) (seed l) (K l) (Tsec l) Z ξ) :
    Squarefree (physicalHistoryCode slots s R seed K Tsec Z ξ first r).2.1 ∧
      (physicalHistoryCode slots s R seed K Tsec Z ξ first r).2.1 ∣
        (physicalHistoryCode slots s R seed K Tsec Z ξ first r).1.2.1.1 := by
  have hgates := actual_common_gates (s r.1) (R r.1) (seed r.1) (hseed r.1) (hz₁ r.1) (hz₂ r.1)
    r.2.1.val.val.1 r.2.1.val.val.2 r.2.1.val.property
  exact ⟨hseed r.1, hgates.2.2.2.1⟩

/-- The code of a new physical block retains its complete ancestor key as its first coordinate. -/
def appendPhysicalHistoryCode {P α : Type*} [Fintype α] [DecidableEq α] (Label : P → Type*)
    (slots : ∀ p, Label p → Finset α) (s : ∀ p (l : Label p), Input (slots p l))
    (R seed : ∀ p, Label p → Ideal O) (K Tsec : ∀ p, Label p → ℝ) (Z ξ : ℝ)
    (first : ∀ p, Label p → FirstSourceLabel)
    (r : (p : P) × (l : Label p) × ActualSecondBlockIndex (s p l) (R p l) (seed p l) (K p l) (Tsec p l) Z ξ) :
    P × DecoratedPrefix :=
  (r.1, physicalHistoryCode (slots r.1) (s r.1) (R r.1) (seed r.1) (K r.1) (Tsec r.1) Z ξ (first r.1) r.2)

theorem appendPhysicalHistoryCode_injective {P α : Type*} [Fintype α] [DecidableEq α] (Label : P → Type*)
    (slots : ∀ p, Label p → Finset α) (s : ∀ p (l : Label p), Input (slots p l))
    (R seed : ∀ p, Label p → Ideal O) (K Tsec : ∀ p, Label p → ℝ) (Z ξ : ℝ)
    (first : ∀ p, Label p → FirstSourceLabel)
    (hfirst : ∀ p, Function.Injective (fun l => (first p l, seed p l))) :
    Function.Injective (appendPhysicalHistoryCode Label slots s R seed K Tsec Z ξ first) := by
  rintro ⟨p,r⟩ ⟨p',r'⟩ h
  have hp : p = p' := congrArg Prod.fst h
  subst p'
  have hr := physicalHistoryCode_injective (slots p) (s p) (R p) (seed p) (K p) (Tsec p) Z ξ (first p)
    (hfirst p) (congrArg Prod.snd h)
  exact Sigma.ext rfl (heq_of_eq hr)

#print axioms physicalHistoryCode_injective
#print axioms physicalHistoryCode_seed
#print axioms appendPhysicalHistoryCode_injective
end
end OAI.SevenEighths.Cycle153JointCount
