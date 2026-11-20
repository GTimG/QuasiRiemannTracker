/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One authentic earlier/native cap bank for all actual P4 witness labels. -/
import Candidate.C092.transport.StrongPairOrdinaryNearBank
import Candidate.C092.transport.StrongPairLowBank

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.WholeSlot
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.LowActual QRH.Cycle092.Source
open QRH.Cycle092.MediumReplace.Source
local notation "O" => ActualEisensteinCubic.O

/-- The cap mesh precedes Slot/arithmetic data. The common source degree,
controls, constant and radius threshold precede the live witness label,
actual dyad, zero, frequency, retained subproduct and physical row family. -/
theorem ordinary_near_independent_bank (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y m0 δ εsource dmin : ℝ} (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hn0 : y ≤ n) (hn1 : n ≤ sourceRatio*y)
    (hm0 : y/(H:ℝ) ≤ m0) (hm01 : m0 ≤ 51/100) (hδ : 0 < δ)
    (hε : 0 < εsource) (hdmin : 0 < dmin) :
    ∃ bank : Finset (ℝ×ℝ),∃ decrement : (ℝ×ℝ)→ℝ,∃ mesh : ℝ,0 < mesh ∧
      (∀ B∈bank,(98/100:ℝ) ≤ B.1 ∧ B.1 ≤ (H:ℝ) ∧ m0 ≤ B.2 ∧ B.2 ≤ 51/100 ∧
        0 < decrement B ∧ decrement B ≤ δ ∧ 0 < nearOrdinaryQuota n B.2 B.1-decrement B) ∧
      (∀ d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
        ∃ B∈bank,B.1 ≤ min d (H:ℝ) ∧ min d (H:ℝ)-B.1 < δ ∧ m ≤ B.2 ∧ B.2-m < δ) ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀ (M : Ideal O) [NeZero M] (Hray : Subgroup (O⧸M)ˣ)
      (hHray : RayOrthogonality.globalUnits M ≤ Hray),
    ∀ W : ℝ→ℂ,ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ bΦ : ℝ,2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ) ⊆ Set.Iic bΦ →
    ∀ (ηLong baseLong η base : Character) (QLong Q : Ideal O),
      QLong ≤ M → internalQ QLong baseLong ≠ 0 → internalQ QLong baseLong ≠ ⊤ →
      internalQ QLong baseLong ≤ Ideal.span {(72:O)} →
      Q ≤ M → internalQ Q base ≠ 0 → internalQ Q base ≠ ⊤ →
      internalQ Q base ≤ Ideal.span {(72:O)} →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0 < C ∧
    ∀ᶠ U : ℝ in atTop,∀ d : ℝ,dmin ≤ d →∀ B∈bank,
    ∀ j : Option (RayQuotient.Characters M Hray × RayQuotient.Characters M Hray),
      PairAt (Slot:=Slot) M Hray hHray (n/B.1) (nearOrdinaryCap n B.2 B.1) (nearOrdinaryQuota n B.2 B.1-decrement B)
        W bΦ mesh εsource (U^d) ηLong (witnessBase M Hray hHray η base j)
          baseLong (witnessBase M Hray hHray base base j) QLong Q degree controls C := by
  obtain ⟨bank,dec,hbank,hnet⟩ := ordinary_near_bank_sources hβ cover hy0 hy1 hn0 hn1 hm0 hm01 hδ
  obtain ⟨mesh,hm,hsource⟩ := pair_finite_bank_mesh bank (fun B=>n/B.1) (fun B=>nearOrdinaryCap n B.2 B.1)
    (fun B=>nearOrdinaryQuota n B.2 B.1-dec B) (fun B hB=>(hbank B hB).2.2.2.2.2.2.2) hε
  refine ⟨bank,dec,mesh,hm,fun B hB=>?_,hnet,?_⟩
  · obtain ⟨h0,h1,h2,h3,h4,h5,h6,_⟩ := hbank B hB
    exact ⟨h0,h1,h2,h3,h4,h5,h6⟩
  intro Slot _ _ M _ Hray hHray W hW hWs bΦ hbΦ hΦs ηLong baseLong η base QLong Q hQLray hQL0 hQLtop hQL72 hQray hQ0 hQtop hQ72
  let Label := Option (RayQuotient.Characters M Hray × RayQuotient.Characters M Hray)
  have hs (j : Label) := pair_finite_bank_metadata bank (fun B=>n/B.1) (fun B=>nearOrdinaryCap n B.2 B.1)
    (fun B=>nearOrdinaryQuota n B.2 B.1-dec B) hsource hdmin Slot M Hray hHray W hW hWs bΦ hbΦ hΦs
    ηLong (witnessBase M Hray hHray η base j) baseLong (witnessBase M Hray hHray base base j) QLong Q
    hQLray hQL0 hQLtop hQL72 hQray
    (by simpa only [witness_internalQ M Hray hHray Q hQray base j] using hQ0)
    (by simpa only [witness_internalQ M Hray hHray Q hQray base j] using hQtop)
    (by simpa only [witness_internalQ M Hray hHray Q hQray base j] using hQ72)
  choose deg ctr C hC hsource using hs
  let degree := Finset.univ.sup deg
  let controls := Finset.univ.biUnion ctr
  let constant := (∑ j : Label,C j)+1
  have hconstant : 0 < constant := by
    have hh := Finset.sum_nonneg (s:=Finset.univ) (f:=C) (fun j _=>(hC j).le)
    dsimp [constant]
    linarith
  refine ⟨degree,controls,constant,hconstant,?_⟩
  have hUall := Filter.eventually_all.mpr hsource
  filter_upwards [hUall,eventually_ge_atTop (1:ℝ)] with U hsource hU
  intro d hd B hB j
  have hdeg : deg j ≤ degree := Finset.le_sup (Finset.mem_univ j)
  have hctr : ctr j ⊆ controls := fun q hq=>Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hq⟩
  have hconst : C j ≤ constant := by
    have hh := Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ j)
    dsimp [constant]
    linarith
  exact pairAt_metadata_mono M Hray hHray (Real.rpow_nonneg (zero_le_one.trans hU) _) (hC j).le
    hconst hdeg hctr (hsource j d hd B hB)

#print axioms ordinary_near_independent_bank
end
end QRH.Cycle092.StrongPair
