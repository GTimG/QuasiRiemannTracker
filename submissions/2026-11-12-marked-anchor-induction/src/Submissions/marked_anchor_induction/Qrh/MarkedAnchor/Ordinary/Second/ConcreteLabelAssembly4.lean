/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 4: the class decomposition of the label part of one split.

* `splitLabel S β ψ χ₀ Q m t Kc R H`: the label part of one residual split (the summand of
  `labelAvg` at one `(B, ξ)`: `S = S0 r`, `β = sourceCoefficient r 1`,
  `ψ = childCharacter τ ξ`, `Kc = 16·K·W_B⁴`, `R = frequencyRadius`, `H = sourceNormCap`).
* `splitLabel_le_classes`: with every dyadic range inside the box `[-M, M]⁴`,
  `splitLabel ≤ ∑_{n ∈ box} ∑_{l : n ∈ range l, block ≠ 0} wt_l(n) ‖labelBlock_l(n)‖`,
  `wt_l(n) = ρ(C)·outerScalar(C, D, Kc, n)·normalizer(C, D, U)` (`nonfixed_block_eq`).
* `labelBlock_rows_filter`: the rows of a class can be restricted to `N(z) < 2^{n₁}` (the row
  annulus of the whole kernel vanishes above), giving the majorization `hmajor` with `H = 2^{n₁}`.
* `labelBlock_ne_zero_column`: a nonzero block has columns `C·I`, `D·J` with nonzero coefficient
  and `N(I) < 2^{n₂}`, `N(J) < 2^{n₃}` (the root windows vanish above).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly3
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteTotalSplit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete

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

/-- The labels `(p, U)` of a residual source. -/
abbrev Lab (S : Finset Id) := Σ p : commonLabels (supportedColumns S) (supportedColumns S),
  Finset (CommonIndex p.val.1 p.val.2)

/-- **The label part of one split.** -/
def splitLabel (S : Finset Id) (β : Id → ℂ) (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t Kc R H : ℝ) : ℝ :=
  ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
    ‖rhoC p.val.1‖ * ∑ U : Finset (CommonIndex p.val.1 p.val.2),
      ∑ n : SourceBlocks p.val.1 p.val.2 U Kc R H,
        ‖physicalBlock ψ t S β p.val.1 p.val.2
          (commonLabels_supported S _ _ p.property).1
          (commonLabels_supported S _ _ p.property).2 U R
          (partRows false ψ χ₀ Q m p.val.1 p.val.2 U R) ballProfile Kc (fun i => (n i : ℤ))‖

/-- The labelled block of a label in the class `n`. -/
def classBlock (S : Finset Id) (β : Id → ℂ) (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O)
    (t Kc R : ℝ) (l : Lab S) (n : Fin 4 → ℤ) : ℂ :=
  labelBlock ψ t S β l.1.val.1 l.1.val.2 (commonLabels_supported S _ _ l.1.property).1
    (commonLabels_supported S _ _ l.1.property).2 l.2 R
    (partRows false ψ χ₀ Q m l.1.val.1 l.1.val.2 l.2 R) ballProfile
    (dyadicScale (n 0) * dyadicScale (n 1) / (dyadicScale (n 2) * dyadicScale (n 3)))
    (fun _ => Real.log (secondEffectiveScale l.1.val.1 l.1.val.2
      (commonFrequencyGenerator l.1.val.1 l.1.val.2 * nonunitFrequencyGenerator l.1.val.1 l.1.val.2 l.2)
        Kc / dyadicScale (n 0)))
    (fun z => Real.log (normValue z / dyadicScale (n 1)))
    (dyadicScale (n 2)) (dyadicScale (n 3))

/-- The class weight `ρ(C)·outerScalar·normalizer`. -/
def classWeight (S : Finset Id) (Kc : ℝ) (l : Lab S) (n : Fin 4 → ℤ) : ℝ :=
  ‖rhoC l.1.val.1‖ * (outerScalar l.1.val.1 l.1.val.2 Kc n * normalizer l.1.val.1 l.1.val.2 l.2)

/-- The dyadic range of a label. -/
def inRange (S : Finset Id) (Kc R H : ℝ) (l : Lab S) (n : Fin 4 → ℤ) : Prop :=
  ∀ i, n i ∈ indices (sourceLower l.1.val.1 l.1.val.2
      (commonFrequencyGenerator l.1.val.1 l.1.val.2 * nonunitFrequencyGenerator l.1.val.1 l.1.val.2 l.2)
        Kc i)
    (sourceUpper l.1.val.1 l.1.val.2
      (commonFrequencyGenerator l.1.val.1 l.1.val.2 * nonunitFrequencyGenerator l.1.val.1 l.1.val.2 l.2)
        Kc R H i)

/-- The box of dyad vectors. -/
def box (M : ℤ) : Finset (Fin 4 → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-M) M)

theorem card_box (M : ℤ) : (box M).card = ((2*M + 1).toNat)^4 := by
  unfold box
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Int.card_Icc, show M + 1 - -M = 2*M + 1 by ring]

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
          (partRows false ψ χ₀ Q m l.1.val.1 l.1.val.2 l.2 R) ballProfile Kc (fun i => (n i : ℤ))‖ =
        classWeight S Kc l (fun i => (n i : ℤ)) *
          ‖classBlock S β ψ χ₀ Q m t Kc R l (fun i => (n i : ℤ))‖ := by
    intro l n
    rw [nonfixed_block_eq ψ t S β _ _ _ _ l.2 R χ₀ Q m ballProfile Kc hKc]
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

/-! ### Kernel vanishing -/

theorem logAnnulus_log_zero (q d : ℝ) (hd : 0 < d) (hq : d ≤ q) :
    logAnnulus (Real.log (q / d)) = 0 := by
  unfold logAnnulus
  rw [Real.exp_log (div_pos (hd.trans_le hq) hd), annulus_zero_high _ ((le_div_iff₀ hd).mpr (by linarith))]
  simp

/-- **Row restriction of a class block.** -/
theorem labelBlock_rows_filter (η : Character) (t : ℝ) (S : Finset Id) (β : Id → ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (r : ℝ) (ρ : O → ℝ) (d X Y : ℝ) (hd : 0 < d) :
    labelBlock η t S β C D hC hD U R rows W r ρ (fun z => Real.log (normValue z / d)) X Y =
      labelBlock η t S β C D hC hD U R (rows.filter (fun z => normValue z < d)) W r ρ
        (fun z => Real.log (normValue z / d)) X Y := by
  unfold labelBlock
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs with h
  · rfl
  · have h0 : logAnnulus (Real.log (normValue z / d)) = 0 := logAnnulus_log_zero _ _ hd (not_lt.mp h)
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero; intro I _
    apply Finset.sum_eq_zero; intro J _
    unfold wholeKernel
    simp [h0]

theorem rows_major (rows : Finset O) (d : ℝ) (hd : 0 < d) :
    ∀ z ∈ rows.filter (fun z => normValue z < d),
      1 ≤ (ballProfile (‖ConcreteTraceCRT.eisEmbedding z‖^2 / d)).re := by
  intro z hz
  exact ballProfile_majorizes d hd z (Finset.mem_filter.mp hz).2.le

/-- **A nonzero block has small columns with nonzero coefficient.** -/
theorem labelBlock_ne_zero_column (η : Character) (t : ℝ) (S : Finset Id) (β : Id → ℂ)
    (C D : Id) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (r : ℝ) (ρ x : O → ℝ) (X Y : ℝ) (hX : 0 < X)
    (hY : 0 < Y)
    (h : labelBlock η t S β C D hC hD U R rows W r ρ x X Y ≠ 0) :
    (∃ I : Id, β (C * I) ≠ 0 ∧ (Ideal.absNorm I : ℝ) < X) ∧
      (∃ J : Id, β (D * J) ≠ 0 ∧ (Ideal.absNorm J : ℝ) < Y) := by
  unfold labelBlock at h
  obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hz' := right_ne_zero_of_mul hz
  obtain ⟨I, _, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz'
  obtain ⟨J, _, hJ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hI
  have hk := right_ne_zero_of_mul hJ
  have hc := right_ne_zero_of_mul (left_ne_zero_of_mul hJ)
  have hβI : β (C * I) ≠ 0 := by
    intro h0; apply hc; simp [h0]
  have hβJ : β (D * J) ≠ 0 := by
    intro h0; apply hc; simp [h0]
  unfold wholeKernel rootWindow at hk
  have hI2 : logAnnulus (Real.log ((Ideal.absNorm (I : Id) : ℝ) / X)) ≠ 0 := by
    intro h0; apply hk; simp [h0]
  have hJ2 : logAnnulus (Real.log ((Ideal.absNorm (J : Id) : ℝ) / Y)) ≠ 0 := by
    intro h0; apply hk; simp [h0]
  refine ⟨⟨I, hβI, ?_⟩, ⟨J, hβJ, ?_⟩⟩
  · by_contra hn
    exact hI2 (logAnnulus_log_zero _ _ hX (not_lt.mp hn))
  · by_contra hn
    exact hJ2 (logAnnulus_log_zero _ _ hY (not_lt.mp hn))

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
