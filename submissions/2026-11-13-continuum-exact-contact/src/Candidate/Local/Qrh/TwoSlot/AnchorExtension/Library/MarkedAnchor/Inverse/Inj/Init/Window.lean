/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Init.AssignedWidth
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Inj.Caller

/-!
# Inverse.Inj.Init.Window — allocated slot widths for the injective allocations

`Init/AssignedWidth` with the pairwise disjointness of the slot lists replaced by the
injectivity of the allocation (the filter `InjQ` of `assignedSourceInj`):

* `allocated_slot_product_inj` — `∏_{J₁} H ≤ 2^|J₁| N(common) N(overlap)` for an INJECTIVE
  allocation `f₁` of `J₁` into `common ∪ overlap` (the bound is false for non-injective
  allocations: several slots may then share one prime);
* `assigned_quotient_cases_inj` — the quotients of `assignedSourceInj` come with injective
  allocations;
* `window_initState_assigned_inj` — the window states of the allocated subcollections are
  initial states at their actual width (no disjointness of the lists).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows InverseInitialCanonicalState
open InverseInitialEnergyCallerAssigned InverseInitialClippedColumns
open Qrh.MarkedAnchor.Inverse
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

/-- The allocated primes bound the allocated slot widths (injective allocation). -/
theorem allocated_slot_product_inj {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
    (nrm : ι → ℝ) (hn : ∀ k, 1 ≤ nrm k) (slots J₁ : Finset σ) (hJ : J₁ ⊆ slots)
    (lists : σ → Finset ι) (H : σ → ℝ)
    (hH : ∀ i ∈ slots, ∀ P ∈ lists i, H i ≤ 2 * nrm P) (hH1 : ∀ i ∈ slots, 1 ≤ H i)
    (common overlap : Finset ι) (f₁ : ∀ i ∈ J₁, ι) (hf₁ : ∀ i (hi : i ∈ J₁), f₁ i hi ∈ lists i)
    (hinjf : InjQ J₁ f₁)
    (hmem : ∀ i (hi : i ∈ J₁), f₁ i hi ∈ common ∪ overlap) :
    (∏ i ∈ J₁, H i) ≤ 2^J₁.card * ((∏ k ∈ common, nrm k) * ∏ k ∈ overlap, nrm k) := by
  have hstep : (∏ i ∈ J₁, H i) ≤ ∏ i ∈ J₁.attach, (2 * nrm (f₁ i.1 i.2)) := by
    rw [← Finset.prod_attach J₁ H]
    exact prod_le_prod_real _ _ _ (fun i _ => zero_le_one.trans (hH1 i.1 (hJ i.2)))
      (fun i _ => hH i.1 (hJ i.2) _ (hf₁ i.1 i.2))
  have hinj : Set.InjOn (fun i : J₁ => f₁ i.1 i.2) (J₁.attach : Set J₁) := by
    intro i _ j _ hij
    exact Subtype.ext (hinjf i.1 i.2 j.1 j.2 hij)
  have himage : (∏ i ∈ J₁.attach, nrm (f₁ i.1 i.2)) =
      ∏ k ∈ J₁.attach.image (fun i : J₁ => f₁ i.1 i.2), nrm k :=
    (Finset.prod_image (f := nrm) hinj).symm
  have hsub : J₁.attach.image (fun i : J₁ => f₁ i.1 i.2) ⊆ common ∪ overlap := by
    intro k hk
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
    exact hmem i.1 i.2
  have hle1 := prod_le_prod_of_subset_one_le nrm hsub (fun k _ => hn k)
  have hle2 := prod_union_le_mul common overlap nrm (fun k _ => hn k)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_attach, himage] at hstep
  have h2 : (0:ℝ) ≤ 2^J₁.card := by positivity
  calc (∏ i ∈ J₁, H i) ≤ 2^J₁.card * ∏ k ∈ J₁.attach.image (fun i : J₁ => f₁ i.1 i.2), nrm k :=
        hstep
    _ ≤ 2^J₁.card * ((∏ k ∈ common, nrm k) * ∏ k ∈ overlap, nrm k) :=
        mul_le_mul_of_nonneg_left (hle1.trans hle2) h2

/-- The quotients of the injective assigned sources come from a source of `Sx` with both
(injective) allocations inside `common ∪ overlap`. -/
theorem assigned_quotient_cases_inj {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → O)
    (Sx : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ) (lists : σ → Finset ι) {t : Ideal O}
    (ht : t ∈ quotientSet p (assignedSourceInj Sx J₁ J₂ lists lists)) :
    ∃ x ∈ Sx, ∃ (f₁ : ∀ i ∈ J₁, ι) (f₂ : ∀ i ∈ J₂, ι),
      t = sourceIdeal p (x.common \ x.divisor) ∧
      (∀ i (hi : i ∈ J₁), f₁ i hi ∈ lists i) ∧ (∀ i (hi : i ∈ J₁), f₁ i hi ∈ x.common ∪ x.overlap) ∧
      InjQ J₁ f₁ ∧
      (∀ i (hi : i ∈ J₂), f₂ i hi ∈ lists i) ∧ (∀ i (hi : i ∈ J₂), f₂ i hi ∈ x.common ∪ x.overlap) ∧
      InjQ J₂ f₂ := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨⟨x,f⟩,hxf,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hxprod,hassign,hinj₁,hinj₂⟩ := Finset.mem_filter.mp hxf
  obtain ⟨hxS,hfpi⟩ := Finset.mem_product.mp hxprod
  obtain ⟨hf₁,hf₂⟩ := Finset.mem_product.mp hfpi
  refine ⟨x,hxS,f.1,f.2,rfl,fun i hi => Finset.mem_pi.mp hf₁ i hi,?_,hinj₁,
    fun i hi => Finset.mem_pi.mp hf₂ i hi,?_,hinj₂⟩
  · intro i hi
    rw [paired_left_mem J₁ J₂ f i hi]
    exact hassign _
  · intro i hi
    rw [paired_right_mem J₁ J₂ f i hi]
    exact hassign _

theorem quotientSet_assignedSourceInj_subset {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
    (p : ι → O) (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    quotientSet p (assignedSourceInj S J₁ J₂ L₁ L₂) ⊆ quotientSet p S :=
  (InverseInitialEnergyCallerUnits.quotientSet_mono p (assignedSourceInj_subset S J₁ J₂ L₁ L₂)).trans
    (InverseInitialEnergyCallerMass.assigned_quotient_subset p S J₁ J₂ L₁ L₂)

/-- `window_initState_assigned` for an injective allocation (no disjointness of the lists). -/
theorem window_initState_assigned_inj {ι : Type} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1<Z)(hη:0≤η)
    (hhi:∀i,hi i≤Z^η)(hdlo:Z^(-η)≤lo 1)
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    {σ:Type}[DecidableEq σ](all assigned:Finset σ)(hassigned:assigned⊆all)
    (q:σ→O)(z a b:σ→ℝ)(W:σ→ℝ→ℂ)
    (hz:∀i∈all,0≤z i)(hq:∀i∈assigned,q i≠0)
    (hW:∀i∈assigned,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hret:∀i∈assigned,W i ((Ideal.absNorm (Ideal.span {q i}):ℝ)/Z^(z i))≠0)
    (hthreshold:(∏i∈assigned,b i)≤Z^η)
    (lists : σ → Finset ι) (Hslot : σ → ℝ) (K : ℕ) (hK : all.card ≤ K)
    (hH1 : ∀ i ∈ all\assigned, 1 ≤ Hslot i)
    (hHlow : ∀ i ∈ all\assigned, ∀ P ∈ lists i,
      Hslot i ≤ 2*(Ideal.absNorm (Ideal.span {p P}) : ℝ))
    (hprod : (∏ i ∈ all\assigned, Hslot i) ≤ Z^(assignedCenter (all\assigned) z+η))
    (hlow : Z^(assignedCenter (all\assigned) z) ≤ ∏ i ∈ all\assigned, Hslot i)
    (hKη : (2:ℝ)^K ≤ Z^η)
    (Sx : Finset (Source (ι:=ι) 0)) (hSx : Sx ⊆ windowSource p S ψ Z D B v θ H)
    (J₁ : Finset σ) (hJ₁ : J₁ ⊆ all\assigned) (x : Source (ι:=ι) 0) (hxS : x ∈ Sx)
    (g : ∀ i ∈ J₁, ι) (hgl : ∀ i (hi : i ∈ J₁), g i hi ∈ lists i)
    (hgm : ∀ i (hi : i ∈ J₁), g i hi ∈ x.common ∪ x.overlap) (hginj : InjQ J₁ g)
    (m r τ Pmax Smax κ:ℝ)(hD:D=r+assignedCenter all z-2*assignedCenter assigned z)
    (hr0:0≤Pmax)(hr:r≤Pmax)(hzS:assignedCenter all z≤Smax)(hm1:1≤m)(hτ0:0≤τ)(hκ:8*η+τ≤κ)
    (hcut:radialCenter m H θ D B≤4*η+τ)
    (hclip:max 0 (D-B-v)-(D-B-v)≤3*η) :
    InitState Pmax Smax κ (max 0 (D-B-v)) (θ+v+2*η) (θ+H+2*η)
      (fullPunctureWidth Z (sourceIdeal p (x.common \ x.divisor)) (assignedElement assigned q))
      (Real.logb Z (∏ i ∈ (all\assigned)\J₁, Hslot i)) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hxw : x ∈ windowSource p S ψ Z D B v θ H := hSx hxS
  have htw : sourceIdeal p (x.common \ x.divisor) ∈ quotientSet p (windowSource p S ψ Z D B v θ H) :=
    Finset.mem_image.mpr ⟨x,hxw,rfl⟩
  have hretained := window_quotient_subset_retained p S ψ Z D B v θ H htw
  have hP: -2*η≤B-θ:=by
    have hn:=(nonempty_radius p hp (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ)
      Z (B-θ) η hZ ⟨_,hretained⟩
      (retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
        (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZ)
        (hψ 0) (hψ 1) (hhi 0) hdlo hdiv)).2
    linarith
  have hreg:=assigned_register all assigned hassigned z hz
  have hj:assignedElement assigned q≠0:=Finset.prod_ne_zero_iff.mpr hq
  have hnj:=assigned_norm_power assigned q z a b W Z η (zero_lt_one.trans hZ) hW hret hthreshold
  obtain ⟨_,_,_,hQ⟩:=retained_full_puncture p hp hpr S ψ D v H
    (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (assignedCenter assigned z) hZ
    (hψ 0) (hψ 1) (hhi 0) hdlo hdiv (assignedElement assigned q) hj hnj htw
  obtain ⟨hV,_⟩:=live_widths_nonnegative p hp hpr S ψ lo hi hψ Z D B v θ H η hZ hhi
    hxw (hf x (Finset.mem_filter.mp hxw).1)
  have hGz : assignedCenter assigned z ≤ assignedCenter all z :=
    Finset.sum_le_sum_of_subset_of_nonneg hassigned (fun i hi _ => hz i hi)
  have hlive : assignedCenter all z - assignedCenter assigned z =
      assignedCenter (all\assigned) z := by
    unfold assignedCenter
    rw [Finset.sum_sdiff_eq_sub hassigned]
  have hcut0 := (Finset.mem_filter.mp hxw).2
  have hψ02 : ψ 0 (((sourceIdeal p x.common).absNorm:ℝ)/Z^B) ≠ 0 ∧
      ψ 2 (((sourceIdeal p x.overlap).absNorm:ℝ)/Z^v) ≠ 0 := by
    have h3 := (mul_ne_zero_iff.mp hcut0).1
    have h2 := mul_ne_zero_iff.mp h3
    exact ⟨(mul_ne_zero_iff.mp h2.1).1, h2.2⟩
  have hcom : ((sourceIdeal p x.common).absNorm:ℝ) ≤ Z^η*Z^B := by
    have h := ((hψ 0) (Function.mem_support.mpr hψ02.1)).2
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hZp _)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hhi 0) (Real.rpow_nonneg hZp.le _))
  have hov : ((sourceIdeal p x.overlap).absNorm:ℝ) ≤ Z^η*Z^v := by
    have h := ((hψ 2) (Function.mem_support.mpr hψ02.2)).2
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hZp _)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hhi 2) (Real.rpow_nonneg hZp.le _))
  let nrm : ι → ℝ := fun k => (Ideal.absNorm (Ideal.span {p k}) : ℝ)
  have hn1 : ∀ k, 1 ≤ nrm k := by
    intro k
    have hne : Ideal.absNorm (Ideal.span {p k}) ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (hp k))
    show (1:ℝ) ≤ (Ideal.absNorm (Ideal.span {p k}) : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  have hJall : J₁ ⊆ all\assigned := hJ₁
  have hprodJ := allocated_slot_product_inj nrm hn1 (all\assigned) J₁ hJall lists Hslot hHlow
    hH1 x.common x.overlap g hgl hginj hgm
  rw [← absNorm_sourceIdeal, ← absNorm_sourceIdeal] at hprodJ
  have hcard : J₁.card ≤ K := (Finset.card_le_card (hJall.trans Finset.sdiff_subset)).trans hK
  have h2K : (2:ℝ)^J₁.card ≤ Z^η :=
    (pow_le_pow_right₀ (by norm_num) hcard).trans hKη
  have hJbound : (∏ i ∈ J₁, Hslot i) ≤ Z^(B+v+3*η) := by
    refine hprodJ.trans ?_
    have e : Z^(B+v+3*η) = Z^η*((Z^η*Z^B)*(Z^η*Z^v)) := by
      rw [show B+v+3*η = η+((η+B)+(η+v)) by ring, Real.rpow_add hZp, Real.rpow_add hZp,
        Real.rpow_add hZp, Real.rpow_add hZp]
    rw [e]
    apply mul_le_mul h2K _ (by positivity) (Real.rpow_nonneg hZp.le _)
    exact mul_le_mul hcom hov (by positivity) (by positivity)
  have hsplit : (∏ i ∈ all\assigned, Hslot i) =
      (∏ i ∈ (all\assigned)\J₁, Hslot i) * ∏ i ∈ J₁, Hslot i :=
    (Finset.prod_sdiff hJall).symm
  have hsub1 : 1 ≤ ∏ i ∈ (all\assigned)\J₁, Hslot i :=
    one_le_prod_real _ Hslot (fun i hi => hH1 i (Finset.mem_sdiff.mp hi).1)
  have hJ1 : 1 ≤ ∏ i ∈ J₁, Hslot i := one_le_prod_real _ Hslot (fun i hi => hH1 i (hJall hi))
  have hlogsplit : Real.logb Z (∏ i ∈ all\assigned, Hslot i) =
      Real.logb Z (∏ i ∈ (all\assigned)\J₁, Hslot i) + Real.logb Z (∏ i ∈ J₁, Hslot i) := by
    rw [hsplit, Real.logb_mul (zero_lt_one.trans_le hsub1).ne' (zero_lt_one.trans_le hJ1).ne']
  have hlogJ : Real.logb Z (∏ i ∈ J₁, Hslot i) ≤ B+v+3*η :=
    (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hJ1)).mpr hJbound
  have hlogJ0 : 0 ≤ Real.logb Z (∏ i ∈ J₁, Hslot i) := Real.logb_nonneg hZ hJ1
  have hall1 : 1 ≤ ∏ i ∈ all\assigned, Hslot i := by rw [hsplit]; nlinarith
  have hlogup : Real.logb Z (∏ i ∈ all\assigned, Hslot i) ≤ assignedCenter (all\assigned) z+η :=
    (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hall1)).mpr hprod
  have hloglo : assignedCenter (all\assigned) z ≤ Real.logb Z (∏ i ∈ all\assigned, Hslot i) :=
    (Real.le_logb_iff_rpow_le hZ (zero_lt_one.trans_le hall1)).mpr hlow
  have hw0 : 0 ≤ Real.logb Z (∏ i ∈ (all\assigned)\J₁, Hslot i) := Real.logb_nonneg hZ hsub1
  have hst := initState_of_window_width Pmax Smax κ m r (assignedCenter all z)
    (assignedCenter assigned z) B θ v H η τ
    (fullPunctureWidth Z (sourceIdeal p (x.common \ x.divisor)) (assignedElement assigned q))
    (Real.logb Z (∏ i ∈ (all\assigned)\J₁, Hslot i))
    hr hzS hm1 hreg.1 hGz hη hτ0 hr0 hκ hP hV hQ (by rw [hD] at hclip; exact hclip)
    (by rw [hD] at hcut; exact hcut) hw0 (by rw [hlive]; linarith) (by rw [hlive]; linarith)
  rw [show r+assignedCenter all z-2*assignedCenter assigned z-B-v = D-B-v by rw [hD]] at hst
  exact hst

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.window_initState_assigned_inj
