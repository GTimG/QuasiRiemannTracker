/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 6: the class objects of one residual split and the root data.

For a residual FP source `s` on `Fin N` (frame source `rs`), the base `ψ = childCharacter P.base ξ`,
and a dyad vector `n`:
* `classLabel n l : BlockLabel` — the label `(p, U)` with its exceptional family
  (`exists_exceptional_family`), rows restricted to the row annulus `N(z) < 2^{n₁}`;
* `frameData g n χ k : LabelData` — the frame label of `(label, t₂)` on the column `g l`
  (`g = p.1` or `p.2`), raised dyad `topDyad(Z^{2a-k+mesh}, N(A₂))`, prefactor `1`;
* `RootLabelData`: every datum the root chain must supply for one split, with the
  per-field lemmas proving the hypotheses of `class_label_bound` from it.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly5

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCompletedRows
open QRH.SilDensitySplit.CubeFree.Packet

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondEnergySplit CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentRestrictedEnergy RayFourExpansion
open CenteredMomentSecondWholeKernel CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondActiveDyadic CenteredMomentMobiusRegroup CenteredMomentSecondExceptionalFamily
open CenteredMomentChildRows CenteredMomentFirstPhysicalSource CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-! ### Label data of a source -/

theorem lab_data (S : Finset Id) (l : Lab S) :
    Supported l.1.val.1 ∧ Supported l.1.val.2 ∧
      CompletedGauss.primeSupport l.1.val.1 = CompletedGauss.primeSupport l.1.val.2 :=
  ⟨(commonLabels_supported S _ _ l.1.property).1, (commonLabels_supported S _ _ l.1.property).2,
    (commonLabels_data _ _ _ _ l.1.property).2.2⟩

/-- The second twist of a label. -/
def lA (S : Finset Id) (l : Lab S) : O := secondTwist l.1.val.1 l.1.val.2 l.2

theorem lA_ne (S : Finset Id) (l : Lab S) : lA S l ≠ 0 :=
  secondTwist_ne_zero _ _ (lab_data S l).1 l.2

/-- The squarefree second Möbius divisors of a label (`BlockLabel.pool`). -/
def labelPool (S : Finset Id) (l : Lab S) : Finset Id :=
  (divisorPool Finset.univ (fun j : sectorPool l.1.val.2 (lab_data S l).2.1.1 S =>
    Ideal.span {sectorElement l.1.val.2 (lab_data S l).2.1.1 S j})).filter Squarefree

/-- The exceptional family of a label over the base `ψ`. -/
def famτ (ψ : Character) (S : Finset Id) (l : Lab S) : RayCharacter → Character :=
  Classical.choose (exists_exceptional_family ψ l.1.val.1 l.1.val.2 (lab_data S l).1
    (lab_data S l).2.1 (lab_data S l).2.2 l.2)

theorem famSpec (ψ : Character) (S : Finset Id) (l : Lab S) :
    Family ψ l.1.val.1 l.1.val.2 (lab_data S l).1 (lab_data S l).2.1 l.2 (famτ ψ S l) :=
  Classical.choose_spec (exists_exceptional_family ψ l.1.val.1 l.1.val.2 (lab_data S l).1
    (lab_data S l).2.1 (lab_data S l).2.2 l.2)

/-- The class rows of a label. -/
def classRows (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (R : ℝ) (S : Finset Id)
    (l : Lab S) (n : Fin 4 → ℤ) : Finset O :=
  (partRows false ψ χ₀ Q m l.1.val.1 l.1.val.2 l.2 R).filter
    (fun z => normValue z < dyadicScale (n 1))

/-- **The `BlockLabel` of a label in the class `n`.** -/
def classLabel (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (Kc R : ℝ) (S : Finset Id)
    (n : Fin 4 → ℤ) (l : Lab S) : BlockLabel ψ χ₀ Q m S where
  C := l.1.val.1
  D := l.1.val.2
  hC := (lab_data S l).1
  hD := (lab_data S l).2.1
  hCD := (lab_data S l).2.2
  U := l.2
  R := R
  rows := classRows ψ χ₀ Q m R S l n
  ρ := fun _ => Real.log (secondEffectiveScale l.1.val.1 l.1.val.2
      (commonFrequencyGenerator l.1.val.1 l.1.val.2 * nonunitFrequencyGenerator l.1.val.1 l.1.val.2 l.2)
        Kc / dyadicScale (n 0))
  x := fun z => Real.log (normValue z / dyadicScale (n 1))
  τ := famτ ψ S l
  hτ := (famSpec ψ S l).height_eq
  hrows := by
    intro z hz
    have hz1 := (Finset.mem_filter.mp hz).1
    rw [partRows_false] at hz1
    exact ⟨sourceRows_nonzero _ _ _ _ z (Finset.mem_filter.mp hz1).1, (Finset.mem_filter.mp hz1).2⟩

theorem classBlock_eq (S : Finset Id) (β : Id → ℂ) (ψ : Character) (χ₀ : RayCharacter) (Q : Id)
    (m : O) (t Kc R : ℝ) (l : Lab S) (n : Fin 4 → ℤ) :
    classBlock S β ψ χ₀ Q m t Kc R l n =
      labelBlock ψ t S β (classLabel ψ χ₀ Q m Kc R S n l).C (classLabel ψ χ₀ Q m Kc R S n l).D
        (classLabel ψ χ₀ Q m Kc R S n l).hC (classLabel ψ χ₀ Q m Kc R S n l).hD
        (classLabel ψ χ₀ Q m Kc R S n l).U (classLabel ψ χ₀ Q m Kc R S n l).R
        (classLabel ψ χ₀ Q m Kc R S n l).rows ballProfile
        (dyadicScale (n 0) * dyadicScale (n 1) / (dyadicScale (n 2) * dyadicScale (n 3)))
        (classLabel ψ χ₀ Q m Kc R S n l).ρ (classLabel ψ χ₀ Q m Kc R S n l).x
        (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  unfold classBlock
  exact labelBlock_rows_filter ψ t S β _ _ _ _ l.2 R _ ballProfile _ _ _ _ _ (dyadicScale_pos _)

theorem classLabel_pool (ψ : Character) (χ₀ : RayCharacter) (Q : Id) (m : O) (Kc R : ℝ)
    (S : Finset Id) (n : Fin 4 → ℤ) (l : Lab S) :
    (classLabel ψ χ₀ Q m Kc R S n l).pool = labelPool S l := rfl

/-! ### Frame labels -/

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- The raised dyad vector of a label in the class `n`. -/
def raisedN (rs : GSrc θ mesh Z) (S : Finset Id) (n : Fin 4 → ℤ) (l : Lab S) : Fin 4 → ℤ :=
  Function.update n 1 (topDyad (Z ^ cutoffLog rs) ((Ideal.span {lA S l}).absNorm : ℝ))

/-- **The frame label data** of `(label, t₂)` on the column `g`. -/
def frameData (j₀ : DictIdx) (ξ : RayCharacter) (s : Source (Fin θ.N) θ.a θ.b)
    (rs : GSrc θ mesh Z) (S : Finset Id) (g : Lab S → Id) (n : Fin 4 → ℤ) (χ : RayCharacter)
    (k : Σ _ : Lab S, Id) : LabelData where
  j := j₀ * ξ * χ
  A₂ := lA S k.1
  n := raisedN rs S n k.1
  R := s.R
  G := g k.1
  seed := 1
  D := k.2
  holesH := s.H
  d := s.d
  prefactor := 1

theorem frameData_eq (j₀ : DictIdx) (ξ : RayCharacter)
    (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z) (S : Finset Id) (g : Lab S → Id)
    (n : Fin 4 → ℤ) (χ : RayCharacter) (k k' : Σ _ : Lab S, Id) (hg : g k.1 = g k'.1)
    (hA : lA S k.1 = lA S k'.1) (hD : k.2 = k'.2) :
    frameData j₀ ξ s rs S g n χ k = frameData j₀ ξ s rs S g n χ k' := by
  unfold frameData raisedN
  rw [hg, hA, hD]

/-- **The root data of one split.** -/
structure RootLabelData {η : Character} (P : SidePack η)
    (Q : Id) (m : O) (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z)
    (Kc R H : ℝ) (M : ℤ) (Mm : ℕ) (clow : ℝ) : Prop where
  hW₁ : rs.W₁ = s.W₁
  hW₂ : rs.W₂ = s.W₂
  ht₁ : rs.t₁ = s.t₁ / (2 * Real.pi)
  ht₂ : rs.t₂ = s.t₂ / (2 * Real.pi)
  hX₁ : rs.X₁ = s.X₁
  hX₂ : rs.X₂ = s.X₂
  hY₁ : rs.Y₁ = s.Y₁
  hY₂ : rs.Y₂ = s.Y₂
  hV₀ : rs.V₀ = P.V
  /-- the first common factor is in the residual puncture (FP `liveSource`: `R = s.R·s.G`) -/
  hCR : P.Cs ∣ s.R
  hcan : Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ s.H s.R s.d
  hQ : internalQ θ.Q θ.η₀ = Q
  hQ72 : Q ≤ Ideal.span {(72:O)}
  hm0 : m ≠ 0
  hml : ConcretePrimeRowBridge.goodLambda ∣ m
  hm2 : (2:O) ∣ m
  /-- the frame Gauss log-scale is the split's Gauss scale -/
  hkLog : Z ^ rs.kLog = Kc
  hKc : 0 < Kc
  hholes_sub : s.H ⊆ ReferencePrimeEnclosure.enclosure (θ.Cap * Z^θ.Lcap)
  hholes_R₀ : ∀ i, ∀ P ∈ s.H, P.val ∈ rs.R₀ i
  /-- the radical cap on both genuine columns of every label and every second divisor -/
  hcapC : ∀ l : Lab (S0 s ha), ∀ Lp ∈ labelPool (S0 s ha) l,
    (Ideal.absNorm (∏ I ∈ QRH.Record1252270103KernelMass.primeSupport ((s.R * l.1.val.1) * Lp) ∪
      holes s.H, I) : ℝ) ≤ Z^θ.Bmask
  hcapD : ∀ l : Lab (S0 s ha), ∀ Lp ∈ labelPool (S0 s ha) l,
    (Ideal.absNorm (∏ I ∈ QRH.Record1252270103KernelMass.primeSupport ((s.R * l.1.val.2) * Lp) ∪
      holes s.H, I) : ℝ) ≤ Z^θ.Bmask
  /-- cube-free genuine factors -/
  hcubeExp : ∀ l : Lab (S0 s ha), ∀ P, leftExponent l.1.val.1 l.1.val.2 P ≤ 2 ∧
    rightExponent l.1.val.1 l.1.val.2 P ≤ 2
  hcubeRadC : ∀ l : Lab (S0 s ha),
    l.1.val.1 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.1, P)^2
  hcubeRadD : ∀ l : Lab (S0 s ha),
    l.1.val.2 ∣ (∏ P ∈ IdealMobiusDivisorSum.primeSupport l.1.val.2, P)^2
  /-- every dyadic range in the box `[-M, M]⁴` -/
  hbox : ∀ l n, inRange (S0 s ha) Kc R H l n → n ∈ box M
  /-- the retained rows lie below the Poisson cutoff of the frame source -/
  hdyad : 32 * R ≤ Z ^ cutoffLog rs
  /-- the column-norm lower bound `N(d₁)N(d₂)·N(I) ≥ c·vol` on nonzero coefficients
  (`hcol_of_canonical`, `c = a²`) -/
  hclow_pos : 0 < clow
  hcol : ∀ I, sourceCoefficient s ha 1 I ≠ 0 →
    clow * rs.vol ≤ ((s.d.1.absNorm : ℝ) * (s.d.2.absNorm : ℝ)) * (Ideal.absNorm I : ℝ)
  /-- the twist is determined by its ideal on the labels -/
  hspanInj : ∀ l l' : Lab (S0 s ha), Ideal.span {lA (S0 s ha) l} = Ideal.span {lA (S0 s ha) l'} →
    lA (S0 s ha) l = lA (S0 s ha) l'
  /-- multiplicities of the labels with a given column and twist -/
  hmultC : ∀ (G : Id) (A : O),
    ((Finset.univ : Finset (Lab (S0 s ha))).filter
      (fun l => l.1.val.1 = G ∧ lA (S0 s ha) l = A)).card ≤ Mm
  hmultD : ∀ (G : Id) (A : O),
    ((Finset.univ : Finset (Lab (S0 s ha))).filter
      (fun l => l.1.val.2 = G ∧ lA (S0 s ha) l = A)).card ≤ Mm

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
