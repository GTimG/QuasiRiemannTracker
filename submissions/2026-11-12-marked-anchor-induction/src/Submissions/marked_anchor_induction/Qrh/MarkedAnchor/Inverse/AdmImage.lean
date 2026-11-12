/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Chain
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.AdmDef

/-!
# Inverse.AdmImage — the slot filter is the dictionary image of the slot class

`imageAdm fam mesh` (`AdmDef`) admits canonical slot data `(q, D, σ, slots, lists, H, a, Z)`
exactly when they are the `DirectAdm` dictionary image of a `fam`-slot vector of mesh `≤ mesh`
(with the native slot hypotheses: primes, ratio `N P / Z^ell ∈ [1,2]`, `‖β‖ ≤ 1`, deletion gate):
there are `data, L, ell, β, J, t` with `q = deletedPeriod (basePeriod data)`,
`slots = {i | i ∉ J}`, `lists i = {P | P.val ∈ L i}`, `H i = 2 Z^(ell i)` and
`a i P = star (β i P / idealCoeff (deletedBase data) P) · logPhase (-t) (log (N P / Z^(ell i)))`.

The dependence of the pool type on `q` is avoided by stating everything through `P.val`; the
covering `imageAdm'_covers` then holds with `q := deletedPeriod (basePeriod data)` definitionally.

* `imageAdm'_covers`, `oracleChainSep'_image`: the separated (disjoint-pool) chain for the image
  filter.
* `oracleChain'_image`: `OracleChain'` for the image filter from the injective chain
  `OracleChainInj'` (Chain.lean).
* `inverse_reduction_excess_canonical_stage'`: the target theorem, conditional on the selection
  reduction and on `OracleChainInj'`. (The route used by the driver is
  `Inj.inverse_reduction_excess_canonical_stage`, with the injective oracle.)
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseMarkedReference
open DetectorDictionaryInverseRawConjugateGates InverseInitialExcludedPeriod
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-- The image filter covers every disjoint-pool slot vector of the family, per class
(`AdmCovers'`). -/
theorem imageAdm'_covers (fam : SlotClass → Prop) (hmono : ∀ cls, fam cls → HeightMono cls) :
    AdmCovers' fam imageAdm' := by
  intro mesh _ cls hcls ι _ _ data L ell β Z hv hv0 hc hell hm hp _ hratio hβ hlarge J Dpool t
  dsimp only [imageAdm', imageAdm]
  refine ⟨cls,rfl,data,L,ell,β,J,t,
    hmono cls hcls ι data L ell β Z hv (hv+|t|) (le_add_of_nonneg_right (abs_nonneg t)) hc,
    hell,hm,hp,hratio,hβ,hlarge,rfl,?_,?_,fun _ => rfl,fun _ _ => rfl,
    le_add_of_nonneg_left hv0⟩
  · intro i
    simp
  · intro i P
    simp [InverseInitialCommonLists.poolList]

/-- The separated (disjoint-pool) chain for the image filter. -/
theorem oracleChainSep'_image (fam : SlotClass → Prop) (hmono : ∀ cls, fam cls → HeightMono cls)
    (Pmax Smax κ : ℝ) (hP : 0 ≤ Pmax)
    (hS : 0 ≤ Smax) (hκ : 0 < κ) (hsum : Pmax+Smax+κ < 1)
    (horacle : OracleOn' imageAdm' fam (InitState Pmax Smax κ)) :
    UniformInverseRectSourceSep fam ⟨Pmax, Smax⟩ :=
  oracleChainSep'_of_covers fam imageAdm' (imageAdm'_covers fam hmono) Pmax Smax κ hP hS hκ hsum horacle

/-- `OracleChain'` for the image filter, from the injective chain and `full_le_inj_energy`. -/
theorem oracleChain'_image (hinj : OracleChainInj' canonicalFamily imageAdm') :
    OracleChain' canonicalFamily imageAdm' :=
  oracleChain'_of_inj canonicalFamily imageAdm' canonicalFamily_embClosed hinj

/-- **Target theorem, excess form, canonical family, per-class filter**, conditional on
`SelectionReductionExcess' canonicalFamily canonicalFamily imageAdm'` and the injective chain
`OracleChainInj' canonicalFamily imageAdm'`. -/
theorem inverse_reduction_excess_canonical_stage'
    (hinj : OracleChainInj' canonicalFamily imageAdm')
    (hsel : SelectionReductionExcess' canonicalFamily canonicalFamily imageAdm')
    (H r s κ : ℝ) (hH : 47/50 ≤ H) (hH1 : H ≤ 1) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/1000) (hdiag : r+s+4*((1-H)/6)+10*κ < 1)
    (hchild : Leaf.UniformInverseRectSourceExcess canonicalFamily (childRect r s ((1-H)/6) κ)
      (((1-H)/6)/(1-6*((1-H)/6)-κ))) :
    UniformInverseRectSource canonicalFamily ⟨r, s⟩ :=
  inverse_reduction_excess_stage' canonicalFamily canonicalFamily imageAdm' imageAdm'_mono
    (oracleChain'_image hinj) hsel H r s κ hH hH1 hr hs hκ hκ1 hdiag hchild

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.inverse_reduction_excess_canonical_stage'
#print axioms Qrh.MarkedAnchor.Inverse.oracleChainSep'_image
