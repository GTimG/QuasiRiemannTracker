/- Copyright (c) 2026 Sil. Apache-2.0.
exact reindexing of PR69's actual CountScheme envelope to the finite
Option(Fin 17) certificate. No source, moment or incumbent bound is assumed.
Not imported into src and not Lean checked. -/
import Candidate.SilPrior.FourthPower.ReturnWindows
import Mathlib.Data.List.OfFn

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReturnEnvelopeBridge
noncomputable section
open ReturnCountData ReturnFinite ReturnWindows

/-- This is the actual upstream list, with our concrete CountScheme instance. -/
def upstreamBranches : List QRH.Record12518109Return.Branch :=
  @QRH.Record1252270103Return.GenericCount.admittedBranches countScheme

/-- This is the actual upstream envelope, not a similar replacement definition. -/
def upstreamEnvelope (k δ p : ℝ) : ℝ :=
  @QRH.Record1252270103Return.GenericCount.envelope countScheme k δ p

/-- Only the old branch varies with k. The seventeen improved windows stay fixed. -/
def variableWindowValue (k δ p : ℝ) (i : Option (Fin 17)) : ℝ := by
  classical
  exact match i with
    | none => oldN k δ p/oldJ k δ p
    | some j => if (window j).Contains δ p then count (window j).branch δ p
      else oldN k δ p/oldJ k δ p

def variableEnvelope (k δ p : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (variableWindowValue k δ p)

theorem variableEnvelope_at_target (δ p : ℝ) :
    variableEnvelope kappa δ p = ReturnFinite.envelope δ p := rfl

/-- Exact equality of our old rational formula with the base in PR69's list. -/
theorem old_count_eq_upstream {k δ p : ℝ} (hk : 7/10 ≤ k)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    oldN k δ p/oldJ k δ p = QRH.Record12518109Return.countingR k δ p := by
  have h3 : 0 < 3*k := by linarith
  have hp3 : p/(3*k) ≤ 1/2 := (div_le_iff₀ h3).2 (by linarith [hp.2])
  have hD : 0 < oldD k p := by
    have he : 2*p/(3*k) = 2*(p/(3*k)) := by ring
    dsimp only [oldD]
    rw [he]
    linarith [hp.2]
  have hJ := old_denominator_positive hk hδ.1 hδ.2 hp.1 hp.2
  have hc : QRH.Record12518109Return.countingCoefficient k p = oldC k p/oldD k p := by
    simpa only [oldC,oldD] using QRH.Record12518109Return.canonical_counting_formula hk
  have hratio : V δ+δ*(oldC k p/oldD k p) = oldJ k δ p/oldD k p := by
    dsimp only [oldJ]
    field_simp [hD.ne']
    <;> ring
  rw [old_count_formula hJ.ne']
  unfold QRH.Record12518109Return.countingR QRH.Record12518109Return.rowDen
  rw [hc]
  change 1-δ+δ*oldC k p*V δ/(2*oldJ k δ p) =
    1-δ+δ*(oldC k p/oldD k p)*V δ/(2*(V δ+δ*(oldC k p/oldD k p)))
  rw [hratio]
  field_simp [hD.ne',hJ.ne']
  <;> ring

theorem upstreamBranches_mem_iff (b : QRH.Record12518109Return.Branch) :
    b ∈ upstreamBranches ↔ ∃ i : Fin 17, b = (admittedWindow i).toBranch := by
  change b ∈ (List.ofFn admittedWindow).map
    QRH.Record1252270103Return.AdmittedWindow.toBranch ↔ _
  constructor
  · intro hb
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    obtain ⟨i,hi⟩ := (List.mem_ofFn' admittedWindow w).mp hw
    subst w
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    apply List.mem_map.mpr
    exact ⟨admittedWindow i,(List.mem_ofFn' admittedWindow _).mpr ⟨i,rfl⟩,rfl⟩

theorem variableEnvelope_le_old (k δ p : ℝ) :
    variableEnvelope k δ p ≤ oldN k δ p/oldJ k δ p := by
  classical
  simpa only [variableEnvelope,variableWindowValue] using
    (Finset.inf'_le (variableWindowValue k δ p)
      (Finset.mem_univ (none : Option (Fin 17))))

theorem variableEnvelope_le_window (k δ p : ℝ) (i : Fin 17)
    (hi : (window i).Contains δ p) :
    variableEnvelope k δ p ≤ count (window i).branch δ p := by
  classical
  simpa only [variableEnvelope,variableWindowValue,if_pos hi] using
    (Finset.inf'_le (variableWindowValue k δ p) (Finset.mem_univ (some i)))

theorem upstreamEnvelope_le_old {k δ p : ℝ} (hk : 7/10 ≤ k)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    upstreamEnvelope k δ p ≤ oldN k δ p/oldJ k δ p := by
  rw [old_count_eq_upstream hk hδ hp]
  exact QRH.Record12518109Return.finiteEnvelope_le_base
    QRH.Record12518109Return.countingR upstreamBranches k δ p

theorem upstreamEnvelope_le_window (k δ p : ℝ) (i : Fin 17)
    (hi : (window i).Contains δ p) :
    upstreamEnvelope k δ p ≤ count (window i).branch δ p := by
  have hm : (admittedWindow i).toBranch ∈ upstreamBranches :=
    (upstreamBranches_mem_iff _).2 ⟨i,rfl⟩
  exact QRH.Record12518109Return.finiteEnvelope_le_branch
    QRH.Record12518109Return.countingR hm hi

/-- Equality for every admissible feedback k, with the exact same fixed windows. -/
theorem upstreamEnvelope_eq_variable {k δ p : ℝ} (hk : 7/10 ≤ k)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    upstreamEnvelope k δ p = variableEnvelope k δ p := by
  classical
  apply le_antisymm
  · change upstreamEnvelope k δ p ≤
      Finset.univ.inf' Finset.univ_nonempty (variableWindowValue k δ p)
    apply Finset.le_inf'
    intro i _hi
    cases i with
    | none => exact upstreamEnvelope_le_old hk hδ hp
    | some i =>
      by_cases hi : (window i).Contains δ p
      · simpa only [variableWindowValue,if_pos hi] using upstreamEnvelope_le_window k δ p i hi
      · simpa only [variableWindowValue,if_neg hi] using upstreamEnvelope_le_old hk hδ hp
  · change variableEnvelope k δ p ≤ QRH.Record12518109Return.finiteEnvelope
      QRH.Record12518109Return.countingR upstreamBranches k δ p
    rcases QRH.Record12518109Return.finiteEnvelope_attained
      QRH.Record12518109Return.countingR upstreamBranches k δ p with ho | ⟨b,hb,ha,he⟩
    · rw [ho,←old_count_eq_upstream hk hδ hp]
      exact variableEnvelope_le_old k δ p
    · obtain ⟨i,rfl⟩ := (upstreamBranches_mem_iff b).1 hb
      rw [he]
      exact variableEnvelope_le_window k δ p i ha

/-- This equality connects the actual count theorem to the already certified
return envelope at the target parameter; no exponent comparison is substituted. -/
theorem upstreamEnvelope_at_target {δ p : ℝ}
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    upstreamEnvelope kappa δ p = ReturnFinite.envelope δ p := by
  rw [upstreamEnvelope_eq_variable (by norm_num [kappa,theta]) hδ hp,
    variableEnvelope_at_target]

/-- The existing one-sided feedback estimate now applies to our reindexed
envelope, with no changing windows and no analytic count hypothesis. -/
theorem variableEnvelope_gap {a k δ p : ℝ} (ha : 7/10 ≤ a) (hak : a ≤ k)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    variableEnvelope k δ p-variableEnvelope a δ p ≤ (5/12)*((k-a)/18) := by
  rw [←upstreamEnvelope_eq_variable (ha.trans hak) hδ hp,
    ←upstreamEnvelope_eq_variable ha hδ hp]
  exact QRH.Record12518109Return.envelope_gap upstreamBranches ha hak
    ⟨hδ.1,by linarith [hδ.2]⟩ hp

theorem variableEnvelope_gap_from_target {k δ p : ℝ} (hk : kappa ≤ k)
    (hδ : δ ∈ Set.Icc 0 (3/4)) (hp : p ∈ Set.Icc 0 (1/2)) :
    variableEnvelope k δ p-ReturnFinite.envelope δ p ≤ (5/12)*((k-kappa)/18) := by
  rw [←variableEnvelope_at_target]
  exact variableEnvelope_gap (by norm_num [kappa,theta]) hk hδ hp

end
end Candidate.SilPrior.FourthPower.ReturnEnvelopeBridge
