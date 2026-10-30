/-
Splitting a radial energy over the sixth-root classes of its rows.

Every nonzero row is uniquely `u·g(r)⁶` with a sixth-free core `u` and a root ideal `r`
(`sixthFrequencyEquiv`). On a compactly supported radial weight the energy is a finite sum, and it splits
over any finite set of roots containing the roots of its rows (`radial_root_split`). The cores of one root class
form a finite set (`classCores`).
-/
import Submissions.arvi_selected_leaf.R1.Reflected
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SixthDecomposition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Poisson.PrincipalTruncation

set_option autoImplicit false
namespace QRH.ArviSelectedLeaf.R1
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open CenteredMomentOriginalRadialComparison
open HeckeInverseAmplification ProbePhysical
local notation "O" => ActualEisensteinCubic.O

/-- The sixth-root class of a nonzero row (the unit class for the zero row). -/
def rootOf (z : O) : HeckeInverseAmplification.NonzeroIdeal :=
  if h : z ≠ 0 then (sixthFrequencyEquiv.symm ⟨z, h⟩).2 else ⟨1, one_ne_zero⟩

theorem rowMap_rootOf (z : O) (hz : z ≠ 0) : ∃ u : FreeRow, z = rowMap (u, rootOf z) := by
  refine ⟨(sixthFrequencyEquiv.symm ⟨z, hz⟩).1, ?_⟩
  have h := congrArg Subtype.val (sixthFrequencyEquiv.apply_symm_apply ⟨z, hz⟩)
  rw [sixthFrequencyEquiv_apply] at h
  simp only [rootOf, dite_eq_left_of_eq_true (eq_true hz), rowMap]
  exact h.symm

theorem rootOf_rowMap (p : FreeRow × HeckeInverseAmplification.NonzeroIdeal) :
    rootOf (rowMap p) = p.2 := by
  have hz := rowMap_ne_zero p
  have hp : sixthFrequencyEquiv.symm ⟨rowMap p, hz⟩ = p := by
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext (sixthFrequencyEquiv_apply p).symm
  simp only [rootOf, dite_eq_left_of_eq_true (eq_true hz), hp]

/-- **Splitting a radial energy over classes.** -/
theorem radial_root_split (F : O → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K bΦ : ℝ) (hK : 0 < K)
    (hsupp : Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ) (hnz : ∀ z, keep z → z ≠ 0)
    {γ : Type*} (ρ : O → γ) (R : Finset γ)
    (hR : ∀ z, keep z → Φ (‖eisEmbedding z‖^2/K) ≠ 0 → ρ z ∈ R) :
    radialEnergy F keep Φ K = ∑ r ∈ R, radialEnergy F (fun z => keep z ∧ ρ z = r) Φ K := by
  set Dk := ConcretePrimeRowBridge.rowNormDisk ⌊max 0 (bΦ * K)⌋₊ with hDk
  have hf : ∀ (P : O → Prop), (∀ z, P z → keep z) → radialEnergy F P Φ K =
      ∑ z ∈ Dk, (if P z then ‖F z‖^2 * (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
    intro P hP
    unfold radialEnergy
    apply tsum_eq_sum
    intro z hz
    split_ifs with hPz
    · have hk := hP z hPz
      by_cases hΦz : Φ (‖eisEmbedding z‖^2/K) = 0
      · rw [hΦz]; simp
      · exfalso
        apply hz
        rw [hDk, TruncatedPrincipalPoisson.mem_rowNormDisk_floor (le_max_left _ _)]
        refine ⟨hnz z hk, ?_⟩
        have h1 := hsupp hΦz
        simp only [Set.mem_Iic] at h1
        rw [div_le_iff₀ hK] at h1
        exact h1.trans (le_max_right _ _)
    · rfl
  rw [hf keep (fun z h => h)]
  have hr : ∀ r ∈ R, radialEnergy F (fun z => keep z ∧ ρ z = r) Φ K =
      ∑ z ∈ Dk, (if keep z ∧ ρ z = r then ‖F z‖^2 * (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
    intro r _
    rw [hf (fun z => keep z ∧ ρ z = r) (fun z h => h.1)]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl hr, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hk : keep z
  · by_cases hΦz : Φ (‖eisEmbedding z‖^2/K) = 0
    · simp [hΦz]
    · have hzR := hR z hk hΦz
      simp only [hk, true_and, ite_true]
      rw [Finset.sum_ite_eq R (ρ z) (fun _ => ‖F z‖^2 * (Φ (‖eisEmbedding z‖^2/K)).re)]
      simp [hzR]
  · simp [hk]

/-- The cores of one root class among the rows of a finite set satisfying a predicate. -/
theorem classCores_injOn (r : HeckeInverseAmplification.NonzeroIdeal) (S : Set O) :
    Set.InjOn (fun u : FreeRow => rowMap (u, r)) ((fun u : FreeRow => rowMap (u, r)) ⁻¹' S) := by
  intro u _ v _ huv
  have h := congrArg Prod.fst (rowMap_injective huv)
  simpa using h

def classCores (D : Finset O) (P : O → Prop) (r : HeckeInverseAmplification.NonzeroIdeal) :
    Finset FreeRow :=
  (D.filter P).preimage (fun u => rowMap (u, r)) (classCores_injOn r _)

theorem mem_classCores (D : Finset O) (P : O → Prop) (r : HeckeInverseAmplification.NonzeroIdeal)
    (u : FreeRow) : u ∈ classCores D P r ↔ rowMap (u, r) ∈ D ∧ P (rowMap (u, r)) := by
  rw [classCores, Finset.mem_preimage, Finset.mem_filter]

/-- Every row of the class is a core of the class. -/
theorem classCores_cover (D : Finset O) (P : O → Prop) (r : HeckeInverseAmplification.NonzeroIdeal)
    (z : O) (hz : z ≠ 0) (hzD : z ∈ D) (hP : P z) (hr : rootOf z = r) :
    ∃ u ∈ classCores D P r, z = rowMap (u, r) := by
  obtain ⟨u, hu⟩ := rowMap_rootOf z hz
  rw [hr] at hu
  refine ⟨u, ?_, hu⟩
  rw [mem_classCores]
  rw [← hu]
  exact ⟨hzD, hP⟩

end
end QRH.ArviSelectedLeaf.R1
