/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual regular-core P4 and authentic rowwise witness source on one finite family. -/
import Candidate.C092.transport.MediumReplaceSourceP4
import Candidate.C092.transport.WitnessRowSupActualP4

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.WitnessRowSup.Actual
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorSupportedWitness ConcretePrimeRowBridge ConcreteTraceCRT HeckeDetectorZeros
open HeckeRowClosure ProbeHighRowFamily CanonicalRowCompletion
open CenteredMomentEnergyBands QRH.Cycle092.WholeSlot
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair
open QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_WitnessP4Apply_94029fb9c7273408_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The P4 constant/order and rowwise constant/order precede the live scale,
state, rows, labels, dyads and zeros. The only analytic source premise is the
fixed-pair source; there is no assumed per-row witness bound or energy bound.
The O-image witness is pulled back by the exact row equivalence, preserving
all its dependent fields. Both displayed energies use the original FreeRows. -/
theorem regular_core_actual_witness
    (bstate Mcap Bmask margin R dmin dmax τ ε e κ heightCost : ℝ)
    (hbstate : 0 ≤ bstate) (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hheight : 4*τ < dmin*heightCost) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hcost : 0 ≤ heightCost) (hbudget : 12*e*(R+2)+8*κ+2*heightCost ≤ ε)
    (profileBound : ℕ→ℝ) (hprofile : ∀ k,0 ≤ profileBound k)
    (controls : Finset (ℕ×ℕ)) :
    ∃ order : ℕ,∃ C4 : ℝ,∃ J : ℕ,∃ Crow : ℝ,0 < C4 ∧ 0 < Crow ∧
    ∀ (η₀ : Character) (I : ℕ),∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
    ∀ s : NaturalState U Bmask bstate,s.width ≤ Mcap →
    ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
      (Qfix : Ideal O),Qfix ≤ M →
      s.mask=fixedBadMask*idealGenerator 1 →
      (∀ z,s.radial.keep z ↔ initialKeep s.character (internalQ Qfix η₀) z) →
    ∀ rows : Finset FreeRow,∀ hrows : ∀ u∈rows,s.radial.keep u.val,
      (∀ u∈rows,s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
    let imageRows := rows.image Subtype.val
    let hk : ∀ z∈imageRows,s.radial.keep z := fun z hz => by
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
      exact hrows u hu
    let F := fun z : imageRows => naturalRow s.character z.val (s.row_ne_zero z.val (hk z.val z.property))
    ∀ (a cutoff r m : ℝ) (i : ℕ),51/100 ≤ a → a ≤ 1 → i ≤ I → 0 ≤ r → r ≤ R →
    ∀ ws : ∀ z : imageRows,SupportedWitness (family M H hH s η₀ (F z)) (U^d) a ε cutoff
      (U^τ) ((U^d)^(τ/(2*dmax))) i,
      (∀ z,(ws z).m=m) →
      (∀ z,zeroMaximum (family M H hH s η₀ (F z))
        (family_nonprincipal M H hH s η₀ hQM hQη (hk z.val z.property) (F z))
        (3*(i+1 : ℕ)*U^τ) < a+2*e) →
    ∀ (WS : rows→ℝ→ℂ) (AS BS σS freqS : rows→ℝ),
      (∀ u,0 < AS u) → (∀ u,Function.support (WS u) ⊆ Icc (AS u) (BS u)) →
      (∀ u,ContDiff ℝ ∞ (WS u)) →
      (∀ u,|freqS u|+U^τ/2 ≤ (3*i+2 : ℕ)*U^τ) →
      (∀ u,∀ x ∈ Icc (1-a-6*e-σS u) (2-σS u),∀ t : ℝ,
        (1+|t|)^2*‖mellin (WS u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
      (∀ u,∀ x ∈ Icc (1-a-6*e-σS u) (2-σS u),∀ t : ℝ,
        (1+|t|)^(order+2)*‖mellin (WS u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound (order+2)) →
    ∀ (N Y l bΦ mesh εsource Csource : ℝ) (W : ℝ→ℂ)
      (j : Option (RayQuotient.Characters M H × RayQuotient.Characters M H)) (degree : ℕ),
      PairAt (Slot:=Slot) M H hH N Y l W bΦ mesh εsource (U^d)
        s.character (witnessBase M H hH s.character η₀ j)
        η₀ (witnessBase M H hH η₀ η₀ j) Qfix Qfix degree controls Csource →
      (∀ z,(ws z).label=j) →
    ∀ (Tslots : Finset Slot) (θ : Slot→RayQuotient.Characters M H)
      (w σslot v : Slot→ℝ) (tMark tLong slotHeight XL : ℝ),
      (∀ k,0 ≤ w k) → (∀ k,w k ≤ mesh) →
      (∀ k,(33/50:ℝ) ≤ σslot k) → (∀ k,σslot k ≤ (33/50:ℝ)) →
      0 ≤ slotHeight → (∀ k,|v k| ≤ slotHeight) → (∑ k∈Tslots,w k) ≤ l →
      0 < XL → length (U^d) XL ≤ N → (∀ u∈rows,rowNorm u ≤ U^d) →
      0 ≤ Csource → length (U^d) ((U^d)^m) ≤ Y →
    ∀ WL : 𝓢(ℝ,ℂ),Function.support (WL:ℝ→ℂ) ⊆ Icc (1/4:ℝ) (9/4) →
    ∀ (weight : rows→ℝ) (Aweight : ℝ),0 ≤ Aweight →
      (∀ u,0 ≤ weight u) → (∀ u,weight u ≤ Aweight) →
      (∑ u : rows,weight u*‖original s.character s.mask 1 u.val.val WL tLong XL*
        original s.character s.mask 1 u.val.val (twistProfile (WS u) (σS u) (freqS u)) 0 ((U^d)^r)*
          (∏ k∈Tslots,normalizedSlot s.character s.mask 1 u.val.val
            (originalPools M H 2 (U^d) w k)
            (originalCoefficients M H hH η₀ θ W (U^d) w σslot v k) tMark ((U^d)^(w k)))‖^2) ≤
        (C4*U^((2*a-1)*(d*r-d*m)+3*d*ε))*
          (12*Aweight*(Csource*QuadraticInitialBound.diagonalControl radialMajorant*
            (1+|tLong|+(|tMark|+|tLong|+slotHeight))^degree*U^(d*(1+εsource)))*
              (sourceControl controls WL)^2*Crow^2*
              (1+(2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i : ℕ)*U^τ))^(2*J+1)) := by
  obtain ⟨order,C4,hC4,hp4⟩ := regular_core_P4 M H hH bstate Mcap Bmask margin R dmin dmax
    τ ε e κ heightCost hbstate hmargin hR hdmin hdmax hτ hheight hε he he' hκ hκ' hcost hbudget profileBound hprofile
  obtain ⟨J,Crow,hCrow,hrow⟩ := actual_witness_rowwise (Slot:=Slot) M H hH controls
  refine ⟨order,C4,J,Crow,hC4,hCrow,?_⟩
  intro η₀ I
  filter_upwards [hp4 η₀ I] with U hU
  refine ⟨hU.1,?_⟩
  intro d hd hd' hds s hs hQM hQη Qfix hQfix hmask hkeep rows hrows hΦ
  dsimp only
  intro a cutoff r m i ha ha' hi hr hr' ws hm hnext WS AS BS σS freqS hAS hWS hsm hfreq hm₂ hmn
    N Y l bΦ mesh εsource Csource W j degree hpair hlabel Tslots θ w σslot v tMark tLong slotHeight XL
    hw hwm hσlo hσhi hh hv hsum hXL hXN hy hCsrc hXY WL hWL weight Aweight hA hweight hweightA
  let er := sourceRowEquiv rows
  let hk : ∀ z∈rows.image Subtype.val,s.radial.keep z := fun z hz => by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact hrows u hu
  have hΦ' : ∀ z∈rows.image Subtype.val,s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 := by
    intro z hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    exact hΦ u hu
  let An : rows→ℂ := fun u=>original s.character s.mask 1 u.val.val WL tLong XL
  let marks : rows→ℂ := fun u=>∏ k∈Tslots,normalizedSlot s.character s.mask 1 u.val.val
    (originalPools M H 2 (U^d) w k)
    (originalCoefficients M H hH η₀ θ W (U^d) w σslot v k) tMark ((U^d)^(w k))
  have hp := hU.2 d hd hd' hds s hs hQM hQη (rows.image Subtype.val) hk hΦ'
    a cutoff r m i ha ha' hi hr hr' ws hm hnext
    (fun z=>WS (er.symm z)) (fun z=>AS (er.symm z)) (fun z=>BS (er.symm z))
    (fun z=>σS (er.symm z)) (fun z=>freqS (er.symm z))
    (fun z=>hAS (er.symm z)) (fun z=>hWS (er.symm z)) (fun z=>hsm (er.symm z))
    (fun z=>hfreq (er.symm z)) (fun z=>hm₂ (er.symm z)) (fun z=>hmn (er.symm z))
    (fun z=>An (er.symm z)) (fun z=>marks (er.symm z)) (fun z=>weight (er.symm z)) (fun _=>false)
    (fun z=>hweight (er.symm z))
  simp only [sourceRow_sum,er,Equiv.symm_apply_apply,sourceRow_val] at hp
  have hUp : 0 < U := zero_lt_one.trans hU.1
  have hwit := hrow U Bmask bstate (U^d) N Y l bΦ mesh εsource Csource W s η₀ Qfix hQfix hmask hkeep j degree hpair
    Tslots θ w σslot v tMark tLong slotHeight XL (Real.rpow_pos_of_pos hUp _) hw hwm hσlo hσhi hh hv hsum
    hXL hXN rows hrows hy d a ε cutoff (U^τ) ((U^d)^(τ/(2*dmax))) m i hUp (by linarith)
    (Real.rpow_nonneg hUp.le _) (Real.rpow_nonneg (Real.rpow_nonneg hUp.le _) _) hCsrc hXY
    (fun u=>ws (sourceRowEquiv rows u)) (fun u=>hlabel _) (fun u=>hm _) WL hWL weight Aweight hA hweight hweightA
  rw [← Real.rpow_mul hUp.le d (1+εsource)] at hwit
  exact P4_finish _ (fun u=>ws (sourceRowEquiv rows u)) weight An
    (fun u=>original s.character s.mask 1 u.val.val (twistProfile (WS u) (σS u) (freqS u)) 0 ((U^d)^r))
    marks (fun _=>false) _ _ (by positivity) hp hwit

#print axioms regular_core_actual_witness
end
end QRH.Cycle092.WitnessRowSup.Actual
