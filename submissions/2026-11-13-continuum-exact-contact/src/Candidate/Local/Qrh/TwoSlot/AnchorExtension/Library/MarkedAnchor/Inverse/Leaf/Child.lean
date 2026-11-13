/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Leaf.Erase

/-!
# Inverse.Leaf.Child — the inverse child by LOW erasure + previous anchor, and HIGH input

The LOW/HIGH split of the INVERSE child. On the child rectangle `ρc` (radius `1`) every row of the
ball is either
* HIGH (`SlotHigh c lam k`: some whole slot above the cut `k`) — paid by the HIGH input
  `InverseHighEnergy fam ρc k x`; or
* LOW — every slot is `≤ c Z^(k ell + lam)`; erase a FIXED set of whole slots (greedy,
  `erasure_choice`) down to retained width `≤ ρp.Smax`, at price
  `Z^(k·(erased width) + K lam) ≤ Z^(k(ρc.Smax - ρp.Smax) + k mesh + K lam)`, and apply the
  PREVIOUS anchor `ρp` to the retained canonical sub-collection over ALL rows of the ball.

The ledger is `k (ρc.Smax - ρp.Smax) ≤ x` (and `0 ≤ x`, `ρc.Pmax ≤ ρp.Pmax`): the output is the
child contract with excess `x`, `UniformInverseRectSourceExcess fam ρc x`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Leaf
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-! ## Scalar helpers -/

/-- The height polynomial is monotone in the degree (slot height `hv ≥ 0`). -/
theorem height_pow_mono (θ : ℝ) {hv : ℝ} (hv0 : 0 ≤ hv) {d d' : ℕ} (h : d ≤ d') :
    ((1+‖θ‖+hv)^d)^2 ≤ ((1+‖θ‖+hv)^d')^2 := by
  have h1 : (1:ℝ) ≤ 1+‖θ‖+hv := by linarith [norm_nonneg θ]
  exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ h1 h) 2

theorem frac_le_quarter (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε) : a * (ε/(4*(a+1))) ≤ ε/4 := by
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  have e : ε * (4*(a+1)) = a*ε*4 + 4*ε := by ring
  rw [e]
  linarith

/-- The LOW ledger with the mesh. -/
theorem low_ledger {k x S Sc Sp m E ε : ℝ} (hk : 0 ≤ k) (hε : 0 ≤ ε)
    (hled : k*(Sc - Sp) ≤ x) (hx : 0 ≤ x) (hS : S ≤ Sc) (hE : E ≤ max 0 (S - Sp + m))
    (hkm : k*m ≤ ε/4) : k*E ≤ x + ε/4 := by
  rcases le_total 0 (S - Sp + m) with h | h
  · rw [max_eq_right h] at hE
    have h1 := mul_le_mul_of_nonneg_left hE hk
    have h2 := mul_le_mul_of_nonneg_left hS hk
    have e1 : k*(S - Sp + m) = k*S - k*Sp + k*m := by ring
    have e2 : k*(Sc - Sp) = k*Sc - k*Sp := by ring
    linarith
  · rw [max_eq_left h] at hE
    have h1 := mul_le_mul_of_nonneg_left hE hk
    rw [mul_zero] at h1
    linarith

/-- Sub-collections of pairwise disjoint slot lists are pairwise disjoint. -/
theorem pairwiseDisjoint_restrict {ι : Type} [Fintype ι] (L : ι → Finset (Ideal O))
    (F : Finset ι) (h : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint L) :
    ((Finset.univ : Finset F) : Set F).PairwiseDisjoint (fun i : F => L i.val) := by
  intro i _ j _ hij
  exact h (Finset.mem_coe.mpr (Finset.mem_univ _)) (Finset.mem_coe.mpr (Finset.mem_univ _))
    (fun e => hij (Subtype.ext e))

/-! ## One scale -/

/-- **The leaf at one scale.** HIGH input and previous anchor at the scale `Z` give the child
contract at `Z` with loss `x + ε`. -/
theorem child_at_scale {cls : SlotClass} (hsubc : SubClosed cls) {ρc ρp : AnchorRect}
    (Φ : ℝ → ℂ) (K : ℕ) {k x ε meshH meshP mesh c CH CP lam Z : ℝ} (data : RowData)
    (dH dP : ℕ) (hk : 0 ≤ k) (hε : 0 ≤ ε) (hx : 0 ≤ x) (hP : ρc.Pmax ≤ ρp.Pmax)
    (hSp : 0 ≤ ρp.Smax) (hled : k*(ρc.Smax - ρp.Smax) ≤ x)
    (hmH : mesh ≤ meshH) (hmP : mesh ≤ meshP) (hkm : k*mesh ≤ ε/4) (hlam : 0 ≤ lam)
    (hKlam : (K:ℝ)*lam ≤ ε/4) (hc : 0 < c) (hCH : 0 ≤ CH) (hCP : 0 ≤ CP) (hZ1 : 1 ≤ Z)
    (hH : InverseHighAt cls ρc Φ K meshH ε Z data dH c lam k x CH)
    (hPv : InverseRectAt cls ρp Φ K meshP 1 1 (ε/2) Z data dP CP) :
    InverseRectAt cls ρc Φ K mesh 1 1 (x+ε) Z data (max dH dP) (CH + (max 1 c)^K * CP) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  have hc1 : 0 < (max 1 c)^K := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 c)) K
  intro ι _ _ hK L ell β hv hv0 hcl hell hmeshi hp hratio hβ hlarge M hM1 hM2 r hadm rows
    hrows θ
  have hM : M = 1 := le_antisymm hM2 hM1
  subst hM
  have hrows' : ∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z := by
    intro u hu
    have h1 := hrows u hu
    rwa [Real.rpow_one] at h1
  have hA0 : 0 ≤ ((1+‖θ‖+hv)^(max dH dP))^2 := by positivity
  -- the split of the rows
  rw [inverseMarkedSum_split data Φ L ell β rows Z r θ (fun u => SlotHigh c lam k Z L ell β u)]
  -- HIGH rows
  have hHigh := hH hK L ell β hv hv0 hcl hell (fun i => (hmeshi i).trans hmH) hp hratio hβ hlarge
    r hadm rows hrows' θ
  have hHigh' : inverseMarkedSum data Φ L ell β
      (rows.filter (fun u => SlotHigh c lam k Z L ell β u)) Z r θ ≤
        CH * Z^(1+(x+ε)) * ((1+‖θ‖+hv)^(max dH dP))^2 := by
    refine hHigh.trans ?_
    rw [show (1:ℝ)+x+ε = 1+(x+ε) by ring]
    exact mul_le_mul_of_nonneg_left (height_pow_mono θ hv0 (le_max_left _ _))
      (mul_nonneg hCH (Real.rpow_nonneg hZ0.le _))
  -- LOW rows: a fixed retained sub-collection of whole slots
  obtain ⟨F, hFS, hFE⟩ := erasure_choice ell mesh ρp.Smax hell hmeshi hSp
  have hlow := low_erasure data Φ L ell β rows
    (rows.filter (fun u => ¬ SlotHigh c lam k Z L ell β u)) (Finset.filter_subset _ _) Z r θ F
    (fun i => c * Z^(k * ell i + lam)) (fun i => mul_nonneg hc.le (Real.rpow_nonneg hZ0.le _))
    (fun u hu i _ => not_slotHigh (Finset.mem_filter.mp hu).2 i)
  -- the previous anchor on the retained sub-collection, over all rows of the ball
  have hcardF : Fintype.card F ≤ K := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_univ F).trans hK
  have hsumF : (∑ i : F, ell i.val) = ∑ i ∈ F, ell i := Finset.sum_coe_sort F ell
  obtain ⟨hr0, hrP, hS0, hSS⟩ := hadm
  have hadmP : ρp.Admissible r (∑ i : F, ell i.val) 1 := by
    rw [hsumF]
    refine ⟨hr0, by linarith, Finset.sum_nonneg (fun i _ => hell i), by linarith⟩
  have hPrev := hPv (ι := F) hcardF (fun i => L i.val) (fun i => ell i.val)
    (fun i => β i.val) hv hv0 (hsubc ι data L ell β Z hv F hcl) (fun i => hell i.val)
    (fun i => (hmeshi i.val).trans hmP) (fun i => hp i.val)
    (fun i => hratio i.val) (fun i => hβ i.val) (fun i => hlarge i.val) 1 le_rfl le_rfl r hadmP
    rows hrows θ
  -- the erasure payment
  have hEcard : (Finset.univ \ F).card ≤ K := (Finset.card_le_univ _).trans hK
  have hpay := erasure_payment_le (Finset.univ \ F) ell c k lam Z K hc.le hlam hZ1 hEcard
  have hkE : k * (∑ i ∈ Finset.univ \ F, ell i) ≤ x + ε/4 :=
    low_ledger hk hε hled hx (by linarith) hFE hkm
  have hpay' : ∏ i ∈ Finset.univ \ F, (c * Z^(k * ell i + lam)) ≤
      (max 1 c)^K * Z^(x + ε/2) := by
    refine hpay.trans (mul_le_mul_of_nonneg_left ?_ hc1.le)
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hP0 : 0 ≤ inverseMarkedSum data Φ (fun i : F => L i.val) (fun i : F => ell i.val)
      (fun i : F => β i.val) rows Z r θ := inverseMarkedSum_nonneg _ _ _ _ _ _ _ _ _
  have hprev' : inverseMarkedSum data Φ (fun i : F => L i.val) (fun i : F => ell i.val)
      (fun i : F => β i.val) rows Z r θ ≤ CP * Z^(1+ε/2) * ((1+‖θ‖+hv)^(max dH dP))^2 :=
    hPrev.trans (mul_le_mul_of_nonneg_left (height_pow_mono θ hv0 (le_max_right _ _))
      (mul_nonneg hCP (Real.rpow_nonneg hZ0.le _)))
  have hexp : Z^(x + ε/2) * Z^(1+ε/2) = Z^(1+(x+ε)) := by
    rw [← Real.rpow_add hZ0]
    congr 1
    ring
  have hLow' : inverseMarkedSum data Φ L ell β
      (rows.filter (fun u => ¬ SlotHigh c lam k Z L ell β u)) Z r θ ≤
        (max 1 c)^K * CP * Z^(1+(x+ε)) * ((1+‖θ‖+hv)^(max dH dP))^2 := by
    refine hlow.trans ((mul_le_mul hpay' hprev' hP0 (by positivity)).trans (le_of_eq ?_))
    rw [← hexp]
    ring
  calc _ ≤ CH * Z^(1+(x+ε)) * ((1+‖θ‖+hv)^(max dH dP))^2 +
        (max 1 c)^K * CP * Z^(1+(x+ε)) * ((1+‖θ‖+hv)^(max dH dP))^2 := add_le_add hHigh' hLow'
    _ = (CH + (max 1 c)^K * CP) * Z^(1+(x+ε)) * ((1+‖θ‖+hv)^(max dH dP))^2 := by ring

/-! ## The leaf -/

/-- **The inverse leaf (generic form).** Previous anchor `ρp` (row-sized) and the HIGH input on
the child rectangle `ρc` give the child contract with excess `x`, provided
`ρc.Pmax ≤ ρp.Pmax`, `0 ≤ ρp.Smax`, `0 ≤ k`, `0 ≤ x` and the LOW ledger
`k (ρc.Smax - ρp.Smax) ≤ x`. -/
theorem inverse_child_of_prev (fam : SlotClass → Prop)
    (hsub : ∀ cls, fam cls → SubClosed cls) {ρc ρp : AnchorRect} {k x : ℝ}
    (hk : 0 ≤ k) (hx : 0 ≤ x) (hP : ρc.Pmax ≤ ρp.Pmax) (hSp : 0 ≤ ρp.Smax)
    (hled : k*(ρc.Smax - ρp.Smax) ≤ x)
    (hprev : UniformInverseRectSource fam ρp) (hhigh : InverseHighEnergy fam ρc k x) :
    UniformInverseRectSourceExcess fam ρc x := by
  intro ε hε
  obtain ⟨meshH, hmeshH, hH⟩ := hhigh ε hε
  obtain ⟨meshP, hmeshP, hPv⟩ := hprev (ε/2) (by linarith)
  have hq0 : 0 < ε/(4*(k+1)) := by positivity
  refine ⟨min (min meshH meshP) (ε/(4*(k+1))), lt_min (lt_min hmeshH hmeshP) hq0, ?_⟩
  intro K cls hcls Φ ao bo hao hab hΦs hΦ data
  have hlam0 : 0 < ε/(4*((K:ℝ)+1)) := by positivity
  obtain ⟨dH, c, CH, ZH, hc, hCH, hZH, hbH⟩ :=
    hH K (ε/(4*((K:ℝ)+1))) hlam0 cls hcls Φ ao bo hao hab hΦs hΦ data
  obtain ⟨dP, CP, ZP, hCP, hZP, hbP⟩ := hPv K cls hcls Φ ao bo hao hab hΦs hΦ data
  have hc1 : 0 < (max 1 c)^K := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 c)) K
  refine ⟨max dH dP, CH + (max 1 c)^K * CP, max ZH ZP, by positivity, lt_max_of_lt_left hZH,
    ?_⟩
  intro Z hZ
  have hZH' : ZH ≤ Z := le_trans (le_max_left _ _) hZ
  have hZP' : ZP ≤ Z := le_trans (le_max_right _ _) hZ
  have hkm : k * min (min meshH meshP) (ε/(4*(k+1))) ≤ ε/4 :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hk).trans (frac_le_quarter k ε hk hε.le)
  have hres := @child_at_scale cls (hsub cls hcls) ρc ρp Φ K k x ε meshH meshP
    (min (min meshH meshP) (ε/(4*(k+1)))) c CH CP (ε/(4*((K:ℝ)+1))) Z data dH dP hk hε.le hx
    hP hSp hled ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _))
    hkm hlam0.le (frac_le_quarter (K:ℝ) ε (Nat.cast_nonneg K) hε.le) hc hCH.le hCP.le
    (hZH.le.trans hZH') (@hbH Z hZH') (@hbP Z hZP')
  exact @hres

/-- The leaf for the canonical family. -/
theorem inverse_child_of_prev_canonical {ρc ρp : AnchorRect} {k x : ℝ}
    (hk : 0 ≤ k) (hx : 0 ≤ x) (hP : ρc.Pmax ≤ ρp.Pmax) (hSp : 0 ≤ ρp.Smax)
    (hled : k*(ρc.Smax - ρp.Smax) ≤ x)
    (hprev : UniformInverseRectSource canonicalFamily ρp)
    (hhigh : InverseHighEnergy canonicalFamily ρc k x) :
    UniformInverseRectSourceExcess canonicalFamily ρc x :=
  inverse_child_of_prev canonicalFamily canonicalFamily_subClosed hk hx hP hSp hled hprev hhigh

end
end Qrh.MarkedAnchor.Inverse.Leaf

#print axioms Qrh.MarkedAnchor.Inverse.Leaf.child_at_scale
#print axioms Qrh.MarkedAnchor.Inverse.Leaf.inverse_child_of_prev
#print axioms Qrh.MarkedAnchor.Inverse.Leaf.inverse_child_of_prev_canonical
