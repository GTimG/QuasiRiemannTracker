/- Literal finite reflection partition of a selected physical forest. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.AttachedFamilyHistory
import Candidate.Research.RecursiveAffine.LiteralFamilyReturnedBound
import Candidate.Research.RecursiveAffine.DepthFamilyCoarseBound

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle153SourceReturn Cycle153JointCount

instance prefixBaseFintype : (n : ℕ) → Fintype (PrefixBase n)
  | 0 => inferInstanceAs (Fintype (RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter))
  | n+1 => by
    letI := prefixBaseFintype n
    exact inferInstanceAs (Fintype (PrefixBase n ×
      (RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter)))

instance suffixBaseFintype : ∀ start count (d : SuffixDepth count), Fintype (suffixBase start count d)
  | _, 0, d => nomatch d
  | _, _+1, none => prefixBaseFintype _
  | start, count+1, some d => suffixBaseFintype (start+1) count d

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
variable (hH : RayOrthogonality.globalUnits M ≤ H)
variable {C : SourceContext (α:=α) M H} {j : Fin 4} {N : ReachableNode C j}
variable (F : N.Family hH) {Bsrc : ℝ} {boxes : ℕ → Finset (Fin 4 → ℤ)}
variable (hist : ForestChronology hH N F Bsrc boxes)

/-- Restrict the already selected source family to a reflection word.
Every retained class, multiplier, missing radical and coefficient is the
same one as in the original family. -/
def orientationFamily (word : OrientationWord) : N.Family hH where
  Prefix := fun d => {p : F.Prefix d // hist.word d p = word}
  prefixFintype := fun _ => inferInstance
  multiplier := fun d p => F.multiplier d p.val
  root_divides := fun d p => F.root_divides d p.val
  historyMissing := fun d p => F.historyMissing d p.val
  historyMissing_nonneg := fun d p => F.historyMissing_nonneg d p.val
  part := fun d p => F.part d p.val
  weight := fun d p => F.weight d p.val
  weight_nonneg := fun d p => F.weight_nonneg d p.val

/-- Each fixed reflection partition has exactly the literal chronology
required by the native joint-count consumer. The full-key injection is
derived from the constructed joint word/history injection. -/
def orientationLiteralHistory (word : OrientationWord) :
    LiteralFamilyHistory (orientationFamily hH F hist word)
      (suffixOffset (4-j.val)) (hist.units word) (wordLeft word) Bsrc boxes where
  code := fun d p => hist.code d p.val
  injective := by
    intro d p q hpq
    apply Subtype.ext
    apply hist.injective d
    exact Prod.ext (p.property.trans q.property.symm) hpq
  multiplier := by
    intro d p
    have h := hist.multiplier d p.val
    simpa only [p.property,orientationFamily] using h
  missing := by
    intro d p
    have h := hist.missing d p.val
    simpa only [p.property,orientationFamily] using h
  facts := by
    intro d p
    have h := hist.facts d p.val
    simpa only [p.property] using h

private def orientationEquiv (d : SuffixDepth (4-j.val)) :
    (Σ word : OrientationWord, {p : F.Prefix d // hist.word d p = word}) ≃ F.Prefix d where
  toFun := fun p => p.2.val
  invFun := fun p => ⟨hist.word d p,⟨p,rfl⟩⟩
  left_inv := by
    rintro ⟨word,p,hp⟩
    dsimp only
    cases hp
    rfl
  right_inv := fun _ => rfl

theorem orientationFamily_component_sum (d : SuffixDepth (4-j.val)) :
    (∑ word : OrientationWord, ∑ p, (orientationFamily hH F hist word).weight d p *
      ((orientationFamily hH F hist word).part d p).value) =
    ∑ p, F.weight d p*(F.part d p).value := by
  have h := Fintype.sum_equiv (orientationEquiv hH F hist d)
    (fun p => F.weight d p.2.val*(F.part d p.2.val).value)
    (fun p => F.weight d p*(F.part d p).value) (fun _ => rfl)
  rw [Fintype.sum_sigma] at h
  refine Eq.trans ?_ h
  dsimp only [orientationFamily]
  apply Finset.sum_congr (Finset.ext (fun word =>
    ⟨fun _ => Finset.mem_univ word,fun _ => Finset.mem_univ word⟩))
  intro word hword
  apply Finset.sum_congr (Finset.ext (fun p =>
    ⟨fun _ => Finset.mem_univ p,fun _ => Finset.mem_univ p⟩))
  intro p hp
  rfl

theorem orientationFamily_value_sum :
    (∑ word : OrientationWord, (orientationFamily hH F hist word).value) = F.value := by
  unfold DepthReturnedFamily.value
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  exact orientationFamily_component_sum hH F hist d

/-- Splitting by actual reflection choices has a fixed factor sixteen.
It never multiplies by the number of residual ideals, deleted subsets,
height bins, source configurations, or physical child rows. -/
theorem orientation_component_bound (d : SuffixDepth (4-j.val)) (bound : ℝ)
    (h : ∀ word : OrientationWord,
      ∑ p, (orientationFamily hH F hist word).weight d p *
        ((orientationFamily hH F hist word).part d p).value ≤ bound) :
    ∑ p, F.weight d p*(F.part d p).value ≤ 16*bound := by
  rw [← orientationFamily_component_sum hH F hist d]
  calc
    _ ≤ ∑ _word : OrientationWord, bound := Finset.sum_le_sum (fun word _ => h word)
    _ = 16*bound := by norm_num [OrientationWord, Fintype.card_fun]

end
end OAI.SevenEighths.Cycle153Reachable

#print axioms OAI.SevenEighths.Cycle153Reachable.orientationLiteralHistory
#print axioms OAI.SevenEighths.Cycle153Reachable.orientationFamily_value_sum
#print axioms OAI.SevenEighths.Cycle153Reachable.orientation_component_bound
