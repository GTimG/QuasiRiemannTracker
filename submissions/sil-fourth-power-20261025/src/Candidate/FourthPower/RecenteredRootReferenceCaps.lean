/- Copyright (c) 2026 Sil. Apache-2.0.
Actual restored root scalar/support inputs for the kept reference.
No row or energy estimate is a premise. 
-/
import Candidate.FourthPower.RecenteredRootReferenceEvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RecenteredRootReferenceCaps
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentSourceMass CenteredMomentUncenteredTerminal CenteredMomentSecondHeightFamily
open MixedPrincipalPair MixedPrincipalAllocations
open RestoredRootDictionary RestoredRootEnergy RecenteredRootSetup RecenteredRootReferenceEvent
open ReferencePrimeEnclosure
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _
variable {α:Type u}[Fintype α]
variable (M:Id)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem remaining_card (s:Setup M H α) :
    Fintype.card (remainingSet s.r s.A)≤Fintype.card α :=
  Fintype.card_le_of_injective (fun i:remainingSet s.r s.A=>i.val) Subtype.val_injective

theorem root_product (s:Setup M H α)
    (hn₁:comparisonScale (9/4)<s.Y₁)(hn₂:comparisonScale (9/4)<s.Y₂) :
    (∏i,(s.rootSource hH hn₁ hn₂).P i)=s.Z^(markedWidth M H s) := by
  change (∏i:remainingSet s.r s.A,s.Z^(s.w i.val))=_
  rw [←Real.rpow_sum_of_pos (zero_lt_one.trans s.hZ)]
  rfl

theorem doubled_root_product (s:Setup M H α)
    (hn₁:comparisonScale (9/4)<s.Y₁)(hn₂:comparisonScale (9/4)<s.Y₂) :
    (∏i,2*(s.rootSource hH hn₁ hn₂).P i)=
      (2:ℝ)^Fintype.card (remainingSet s.r s.A)*s.Z^(markedWidth M H s) := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,root_product M H hH s hn₁ hn₂]

/-- Both displayed marked/short-volume inputs of the reference theorem
follow from the same event and the actual short-side inequality. -/
theorem actual_product_caps (s:Setup M H α)(ε:ℝ)(hε:0<ε)
    (hn₁:comparisonScale (9/4)<s.Y₁)(hn₂:comparisonScale (9/4)<s.Y₂)
    (hhigh:RepairedRootParameters.NeedsCentering ε (ordinaryExponent M H s) (markedWidth M H s))
    (η:Character)(bΦ:ℝ)(he:Event (Fintype.card α) η bΦ ε s.Z)
    (X:ℝ)(hX:0<X)(hshort:X≤rootReference M H s ε) :
    (∏i,2*(s.rootSource hH hn₁ hn₂).P i)≤s.Z^(4:ℝ) ∧
      (9/4:ℝ)*X*(∏i,2*(s.rootSource hH hn₁ hn₂).P i)≤s.Z^(4:ℝ) ∧
      (∏i,(s.rootSource hH hn₁ hn₂).P i)≤s.Z^(markedWidth M H s) := by
  have hz:=zero_lt_one.trans s.hZ
  have hf:=actual_face M H s
  have hell:=RepairedRootParameters.centered_spec hε hf hhigh
  have hω:=RepairedRootParameters.omega_spec ε hε
  have hdim:=event_dimension (remaining_card M H s) he
  have hp:0≤(2:ℝ)^Fintype.card (remainingSet s.r s.A):=pow_nonneg (by norm_num) _
  have htwo:(2:ℝ)^Fintype.card (remainingSet s.r s.A)≤s.Z^(RepairedRootParameters.omegaLoss ε):=by
    nlinarith
  have hb:(9/4:ℝ)*2^Fintype.card (remainingSet s.r s.A)≤s.Z^(RepairedRootParameters.omegaLoss ε):=by
    nlinarith
  have hP:0≤s.Z^(markedWidth M H s):=Real.rpow_nonneg hz.le _
  have hpower:(RepairedRootParameters.omegaLoss ε)+markedWidth M H s≤4 := by
    linarith [hf.2.1,hω.2.2.2]
  have hshortPower:RepairedRootParameters.omegaLoss ε+rootExponent M H s ε+markedWidth M H s≤4 := by
    have hl:rootExponent M H s ε<1:=hell.2.2.2.2.2
    linarith [hf.2.1,hω.2.2.2]
  refine ⟨?_,?_,(root_product M H hH s hn₁ hn₂).le⟩
  · rw [doubled_root_product]
    calc
      _≤s.Z^(RepairedRootParameters.omegaLoss ε)*s.Z^(markedWidth M H s):=
        mul_le_mul_of_nonneg_right htwo hP
      _=s.Z^(RepairedRootParameters.omegaLoss ε+markedWidth M H s):=
        (Real.rpow_add hz _ _).symm
      _≤_:=Real.rpow_le_rpow_of_exponent_le s.hZ.le hpower
  · rw [doubled_root_product]
    calc
      _=((9/4:ℝ)*2^Fintype.card (remainingSet s.r s.A))*X*s.Z^(markedWidth M H s):=by ring
      _≤s.Z^(RepairedRootParameters.omegaLoss ε)*rootReference M H s ε*s.Z^(markedWidth M H s):=
        mul_le_mul_of_nonneg_right (mul_le_mul hb hshort hX.le (Real.rpow_nonneg hz.le _)) hP
      _=s.Z^(RepairedRootParameters.omegaLoss ε+rootExponent M H s ε+markedWidth M H s):=by
        unfold rootReference
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
      _≤_:=Real.rpow_le_rpow_of_exponent_le s.hZ.le hshortPower

theorem actual_enclosure_cap (s:Setup M H α)(ε:ℝ)(η:Character)(bΦ Lcap:ℝ)
    (hs:s.Lcap=Lcap)(he:Event (Fintype.card α) η bΦ ε s.Z)
    (hn₁:comparisonScale (9/4)<s.Y₁)(hn₂:comparisonScale (9/4)<s.Y₂) :
    ∀P∈(s.rootSource hH hn₁ hn₂).S,(P.val.absNorm:ℝ)≤s.Z^(Lcap+8) := by
  intro P hP
  change P∈enclosure (16*s.Z^s.Lcap) at hP
  rw [hs] at hP
  have hp: (P.val.absNorm:ℝ)≤16*s.Z^Lcap:=(enclosure_bound _ P hP).2
  have hz:=zero_lt_one.trans s.hZ
  calc
    _≤16*s.Z^Lcap:=hp
    _≤s.Z*s.Z^Lcap:=mul_le_mul_of_nonneg_right he.2.1 (Real.rpow_nonneg hz.le _)
    _=s.Z^(Lcap+1):=by rw [Real.rpow_add hz,Real.rpow_one];ring
    _≤_:=Real.rpow_le_rpow_of_exponent_le s.hZ.le (by linarith)

/-- Enclosure for either an original rectangle or the actual new
reference. The enclosing source geometry itself is never changed here. -/
theorem actual_rectangle_enclosed (s:Setup M H α)
    (hn₁:comparisonScale (9/4)<s.Y₁)(hn₂:comparisonScale (9/4)<s.Y₂)
    (X Y:ℝ)(hX:X≤(s.rootSource hH hn₁ hn₂).U₁)(hY:Y≤(s.rootSource hH hn₁ hn₂).U₂) :
    ∀I,Supported I→((I.absNorm:ℝ)≤(9/4)*X ∨ (I.absNorm:ℝ)≤(9/4)*Y)→
      primeSupport I⊆primeValues (s.rootSource hH hn₁ hn₂).S := by
  let r:=s.rootSource hH hn₁ hn₂
  have cover:OriginalEnclosure r:=(s.rootData hn₁ hn₂).source_original_enclosure hH
  have hd:r.d=(1,1):=rfl
  intro I hI hlen
  apply cover I hI
  rcases hlen with hl|hr
  · left
    simpa only [hd,Prod.fst,map_one,Nat.cast_one,div_one] using
      hl.trans (mul_le_mul_of_nonneg_left hX (by norm_num))
  · right
    simpa only [hd,Prod.snd,map_one,Nat.cast_one,div_one] using
      hr.trans (mul_le_mul_of_nonneg_left hY (by norm_num))

end
end Candidate.FourthPower.RecenteredRootReferenceCaps
