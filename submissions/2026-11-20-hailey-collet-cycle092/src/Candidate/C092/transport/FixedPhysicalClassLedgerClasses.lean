/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M2, label assembly, part 4: the class decomposition of the label part of one split.

* `splitLabel S β ψ χ₀ Q m t Kc R H`: the label part of one residual split (the summand of
  WP-M's `labelAvg` at one `(B, ξ)`: `S = S0 r`, `β = sourceCoefficient r 1`,
  `ψ = childCharacter τ ξ`, `Kc = 16·K·W_B⁴`, `R = frequencyRadius`, `H = sourceNormCap`).
* `splitLabel_le_classes`: with every dyadic range inside the box `[-M, M]⁴`,
  `splitLabel ≤ ∑_{n ∈ box} ∑_{l : n ∈ range l, block ≠ 0} wt_l(n) ‖labelBlock_l(n)‖`,
  `wt_l(n) = ρ(C)·outerScalar(C, D, Kc, n)·normalizer(C, D, U)` (`nonfixed_block_eq`).
* `labelBlock_rows_filter`: the rows of a class can be restricted to `N(z) < 2^{n₁}` (the row
  annulus of the whole kernel vanishes above), giving the majorization `hmajor` with `H = 2^{n₁}`.
* `labelBlock_ne_zero_column`: a nonzero block has columns `C·I`, `D·J` with nonzero coefficient
  and `N(I) < 2^{n₂}`, `N(J) < 2^{n₃}` (the root windows vanish above). -/
import Candidate.C092.transport.FixedPhysicalClassLedgerGroup
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteTotalSplit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace QRH.Cycle092.FixedPhysicalClassLedger
open QRH.SilDensitySplit.CubeFree.Second.Concrete

noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock CenteredMomentSupport
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentActiveSource CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentRestrictedEnergy RayFourExpansion
open CenteredMomentSecondWholeKernel CenteredMomentSecondLocalization CenteredMomentLogDyadic
open CenteredMomentFirstAmplificationChoice CenteredMomentSmooth CenteredMomentSecondActiveDyadic
open CenteredMomentDyadicCount CenteredMomentSecondDyadicPartition
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O


open QRH.SilDensitySplit.CubeFree.Second.ConcreteLabelAssembly

/-- The physical scalar is unchanged by the original fixed-row restriction. -/
theorem fixed_block_eq (η : Character) (t : ℝ) (S : Finset Id) (β : Id→ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (χ₀ : RayCharacter) (Q : Id) (m : O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (n : Fin 4→ℤ) :
    ‖physicalBlock η t S β C D hC hD U R (partRows true η χ₀ Q m C D U R) W K n‖ =
      outerScalar C D K n*normalizer C D U*
        ‖labelBlock η t S β C D hC hD U R (partRows true η χ₀ Q m C D U R) W
          (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
          (fun _=>Real.log (secondEffectiveScale C D
            (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/dyadicScale (n 0)))
          (fun z=>Real.log (normValue z/dyadicScale (n 1)))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ := by
  have hrows : ∀z∈partRows true η χ₀ Q m C D U R,z≠0 := by
    intro z hz
    exact sourceRows_nonzero C D U R z (Finset.mem_filter.mp hz).1
  rw [physicalBlock_eq η t S β C D hC hD U R _ hrows W K hK n,norm_mul,norm_mul,
    Complex.norm_real,Complex.norm_real]
  have h1 : 0≤outerScalar C D K n := by unfold outerScalar;positivity
  have h2 := normalizer_pos C D hC U
  rw [Real.norm_of_nonneg h1,Real.norm_of_nonneg h2.le]
  rfl

/-- **The label part of one split.** -/
def splitLabel (S : Finset Id) (β : Id → ℂ) (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t Kc R H : ℝ) : ℝ :=
  ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
    ‖rhoC p.val.1‖ * ∑ U : Finset (CommonIndex p.val.1 p.val.2),
      ∑ n : SourceBlocks p.val.1 p.val.2 U Kc R H,
        ‖physicalBlock ψ t S β p.val.1 p.val.2
          (commonLabels_supported S _ _ p.property).1
          (commonLabels_supported S _ _ p.property).2 U R
          (partRows true ψ χ₀ Q m p.val.1 p.val.2 U R) ballProfile Kc (fun i => (n i : ℤ))‖

/-- The labelled block of a label in the class `n`. -/
def classBlock (S : Finset Id) (β : Id → ℂ) (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t Kc R : ℝ) (l : Lab S) (n : Fin 4 → ℤ) : ℂ :=
  labelBlock ψ t S β l.1.val.1 l.1.val.2 (commonLabels_supported S _ _ l.1.property).1
    (commonLabels_supported S _ _ l.1.property).2 l.2 R
    (partRows true ψ χ₀ Q m l.1.val.1 l.1.val.2 l.2 R) ballProfile
    (dyadicScale (n 0) * dyadicScale (n 1) / (dyadicScale (n 2) * dyadicScale (n 3)))
    (fun _ => Real.log (secondEffectiveScale l.1.val.1 l.1.val.2
      (commonFrequencyGenerator l.1.val.1 l.1.val.2 * nonunitFrequencyGenerator l.1.val.1 l.1.val.2 l.2)
        Kc / dyadicScale (n 0)))
    (fun z => Real.log (normValue z / dyadicScale (n 1)))
    (dyadicScale (n 2)) (dyadicScale (n 3))

/-- **The class decomposition of the label part of one split.** -/
theorem splitLabel_le_classes (S : Finset Id) (β : Id → ℂ) (ψ : Character) (χ₀ : RayCharacter)
    (Q : Id) (m : O) (t Kc R H : ℝ) (hKc : 0 < Kc) (M : ℤ)
    (hbox : ∀ l : Lab S, ∀ n, inRange S Kc R H l n → n ∈ box M) :
    splitLabel S β ψ χ₀ Q m t Kc R H ≤
      ∑ n ∈ box M, ∑ l ∈ (Finset.univ : Finset (Lab S)).filter
          (fun l => inRange S Kc R H l n ∧ classBlock S β ψ χ₀ Q m t Kc R l n ≠ 0),
        classWeight S Kc l n * ‖classBlock S β ψ χ₀ Q m t Kc R l n‖ := by
  -- rewrite each block
  have hterm : ∀ (l : Lab S) (n : SourceBlocks l.1.val.1 l.1.val.2 l.2 Kc R H),
      ‖rhoC l.1.val.1‖ * ‖physicalBlock ψ t S β l.1.val.1 l.1.val.2
          (commonLabels_supported S _ _ l.1.property).1
          (commonLabels_supported S _ _ l.1.property).2 l.2 R
          (partRows true ψ χ₀ Q m l.1.val.1 l.1.val.2 l.2 R) ballProfile Kc (fun i => (n i : ℤ))‖ =
        classWeight S Kc l (fun i => (n i : ℤ)) *
          ‖classBlock S β ψ χ₀ Q m t Kc R l (fun i => (n i : ℤ))‖ := by
    intro l n
    rw [fixed_block_eq ψ t S β _ _ _ _ l.2 R χ₀ Q m ballProfile Kc hKc]
    unfold classWeight classBlock
    ring
  -- the label part as a sum over labels and source blocks
  have h1 : splitLabel S β ψ χ₀ Q m t Kc R H =
      ∑ l : Lab S, ∑ n : SourceBlocks l.1.val.1 l.1.val.2 l.2 Kc R H,
        classWeight S Kc l (fun i => (n i : ℤ)) *
          ‖classBlock S β ψ χ₀ Q m t Kc R l (fun i => (n i : ℤ))‖ := by
    unfold splitLabel
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro U _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro n _
    exact hterm ⟨p, U⟩ n
  -- the source blocks of a label as a filtered box
  have h2 : ∀ l : Lab S, (∑ n : SourceBlocks l.1.val.1 l.1.val.2 l.2 Kc R H,
        classWeight S Kc l (fun i => (n i : ℤ)) *
          ‖classBlock S β ψ χ₀ Q m t Kc R l (fun i => (n i : ℤ))‖) =
      ∑ n ∈ (box M).filter (fun n => inRange S Kc R H l n),
        classWeight S Kc l n * ‖classBlock S β ψ χ₀ Q m t Kc R l n‖ := by
    intro l
    have hinj : Function.Injective (fun (n : SourceBlocks l.1.val.1 l.1.val.2 l.2 Kc R H) =>
        (fun i => (n i : ℤ))) := by
      intro n n' h
      funext i
      exact Subtype.ext (congrFun h i)
    have himg : (Finset.univ : Finset (SourceBlocks l.1.val.1 l.1.val.2 l.2 Kc R H)).image
        (fun n => (fun i => (n i : ℤ))) = (box M).filter (fun n => inRange S Kc R H l n) := by
      ext n
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
      constructor
      · rintro ⟨n', rfl⟩
        have hr : inRange S Kc R H l (fun i => (n' i : ℤ)) := fun i => (n' i).property
        exact ⟨hbox l _ hr, hr⟩
      · rintro ⟨_, hr⟩
        exact ⟨fun i => ⟨n i, hr i⟩, rfl⟩
    rw [← himg, Finset.sum_image (fun n _ n' _ h => hinj h)]
  rw [h1, Finset.sum_congr rfl (fun l _ => h2 l)]
  have hswap : (∑ l : Lab S, ∑ n ∈ (box M).filter (fun n => inRange S Kc R H l n),
        classWeight S Kc l n * ‖classBlock S β ψ χ₀ Q m t Kc R l n‖) =
      ∑ n ∈ box M, ∑ l ∈ (Finset.univ : Finset (Lab S)).filter (fun l => inRange S Kc R H l n),
        classWeight S Kc l n * ‖classBlock S β ψ χ₀ Q m t Kc R l n‖ := by
    simp only [Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap]
  apply Finset.sum_le_sum; intro n _
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_le_sum; intro l _
  by_cases hr : inRange S Kc R H l n
  · by_cases hb : classBlock S β ψ χ₀ Q m t Kc R l n = 0
    · simp [hr, hb]
    · simp [hr, hb]
  · simp [hr]


#print axioms fixed_block_eq
#print axioms splitLabel_le_classes
end
end QRH.Cycle092.FixedPhysicalClassLedger
