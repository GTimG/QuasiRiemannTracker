/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One degree, finite control set, constant and threshold before U, simultaneously
for every source cap and every actual finite original witness label. -/
import Candidate.C092.transport.RawTicketMiddleSourceBank
set_option autoImplicit false
namespace QRH.Cycle092.RawTicket
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.StrongPair
local notation "O" => ActualEisensteinCubic.O

/-- All labels are actual finite dictionaries, chosen after the early source
mesh but BEFORE U. Caps and labels are selected only after the common eventual
source event. This directly reuses the native finite cap metadata theorem. -/
theorem cap_bank_metadata_all_labels {Index Label : Type*} [DecidableEq Index]
    [Fintype Label] (bank : Finset Index) (N Y l : Index→ℝ)
    {mesh epsilon Vmin : ℝ}
    (hsource : ∀i∈bank,PairUnitBox (N i) (Y i) (l i) mesh epsilon) (hVmin : 0< Vmin)
    (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (bPhi : ℝ) (hbPhi : 2≤ bPhi) (hPhi : Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi)
    (eta1 eta2 base1 base2 : Label→Character) (Q1 Q2 : Label→Ideal O)
    (hQ1ray : ∀j,Q1 j≤ M) (hQ10 : ∀j,internalQ (Q1 j) (base1 j)≠0)
    (hQ1top : ∀j,internalQ (Q1 j) (base1 j)≠⊤)
    (hQ172 : ∀j,internalQ (Q1 j) (base1 j)≤ Ideal.span {(72:O)})
    (hQ2ray : ∀j,Q2 j≤ M) (hQ20 : ∀j,internalQ (Q2 j) (base2 j)≠0)
    (hQ2top : ∀j,internalQ (Q2 j) (base2 j)≠⊤)
    (hQ272 : ∀j,internalQ (Q2 j) (base2 j)≤ Ideal.span {(72:O)}) :
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0< C ∧
    ∀ᶠ U : ℝ in atTop,∀ V : ℝ,Vmin≤ V →∀ i∈bank,∀j : Label,
      PairAt (Slot:=Slot) M H hH (N i) (Y i) (l i) W bPhi mesh epsilon (U^V)
        (eta1 j) (eta2 j) (base1 j) (base2 j) (Q1 j) (Q2 j) degree controls C := by
  have hs (j : Label):=pair_finite_bank_metadata bank N Y l hsource hVmin Slot M H hH
    W hW hWs bPhi hbPhi hPhi (eta1 j) (eta2 j) (base1 j) (base2 j) (Q1 j) (Q2 j)
    (hQ1ray j) (hQ10 j) (hQ1top j) (hQ172 j) (hQ2ray j) (hQ20 j) (hQ2top j) (hQ272 j)
  choose deg ctr C hC hsrc using hs
  let degree:=Finset.univ.sup deg
  let controls:=Finset.univ.biUnion ctr
  let constant:=(∑j : Label,C j)+1
  have hconstant : 0< constant := by
    have hh:=Finset.sum_nonneg (s:=Finset.univ) (f:=C) (fun j _=>(hC j).le)
    dsimp [constant];linarith only [hh]
  refine ⟨degree,controls,constant,hconstant,?_⟩
  have hUall:=Filter.eventually_all.mpr hsrc
  filter_upwards [hUall,eventually_ge_atTop (1:ℝ)] with U hsrc hU
  intro V hV i hi j
  have hd : deg j≤ degree := Finset.le_sup (Finset.mem_univ j)
  have hctr : ctr j⊆controls := fun q hq=> Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hq⟩
  have hc : C j≤ constant := by
    have hh:=Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ j)
    dsimp [constant];linarith only [hh]
  exact pairAt_metadata_mono M H hH (Real.rpow_nonneg (zero_le_one.trans hU) _) (hC j).le
    hc hd hctr (hsrc j V hV i hi)

end
end QRH.Cycle092.RawTicket
#print axioms QRH.Cycle092.RawTicket.cap_bank_metadata_all_labels
