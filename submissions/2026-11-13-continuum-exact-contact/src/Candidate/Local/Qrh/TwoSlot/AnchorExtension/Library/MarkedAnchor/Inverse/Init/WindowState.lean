/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/InitialCanonicalStateWindow.lean`
(Apache-2.0). Modified by Sil (2026-11-11): the native gates `r+2z ≤ m-c₁`, `2r+8z ≤ 3m-c₂` and
the conclusion `CanonicalMargins` are replaced by the parent rectangle `r ≤ Pmax`, `z ≤ Smax`,
`1 ≤ m` and the conclusion `InitState Pmax Smax κ` (Inverse.Oracle). -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalStateWindow
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Oracle

/-!
# Inverse.Init.WindowState — the initial states of a parent rectangle

`window_initState`: every window state of the baseline initialization
(`actual_window_state`) of a parent with free width `r ≤ Pmax`, total mark width `z ≤ Smax`
and ball exponent `m ≥ 1` lies in `InitState Pmax Smax κ` as soon as `8η + τ ≤ κ`, with live
width `z_live = ∑_{unassigned} z + η`. No native gate is used: this stands in for the baseline's
margin computation, the only place where the initialization chain consumes the native gates.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows InverseInitialCanonicalState
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

/-- The arithmetic core: the window-state inequalities give `InitState`. -/
theorem initState_of_window (Pmax Smax κ m r zall G B θ v H η τ Q : ℝ)
    (hr : r ≤ Pmax) (hz : zall ≤ Smax) (hm : 1 ≤ m) (hG : 0 ≤ G) (hGz : G ≤ zall)
    (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hr0 : 0 ≤ Pmax) (hκ : 8*η+τ ≤ κ)
    (hP : -2*η ≤ B-θ) (hV : 0 ≤ θ+v+2*η) (hQ : Q ≤ B-θ+G+3*η)
    (hclip : max 0 (r+zall-2*G-B-v) - (r+zall-2*G-B-v) ≤ 3*η)
    (hcut : radialCenter m H θ (r+zall-2*G) B ≤ 4*η+τ) :
    InitState Pmax Smax κ (max 0 (r+zall-2*G-B-v)) (θ+v+2*η) (θ+H+2*η) Q ((zall-G)+η) := by
  unfold InitState
  unfold radialCenter at hcut
  have hmax := le_max_right 0 (r+zall-2*G-B-v)
  have hmax0 := le_max_left 0 (r+zall-2*G-B-v)
  refine ⟨by linarith, by linarith, ?_, by linarith, by linarith⟩
  -- `N - z_live ≤ r - G + 7η`: either `N = 0` or `N = D-B-v` with `B+v ≥ -4η`
  rcases le_total (r+zall-2*G-B-v) 0 with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h]; linarith

/-- `actual_window_state` without native gates: the window states are initial states. -/
theorem window_initState {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1<Z)(hη:0≤η)
    (hhi:∀i,hi i≤Z^η)(hdlo:Z^(-η)≤lo 1)
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    {σ:Type*}[DecidableEq σ](all assigned:Finset σ)(hassigned:assigned⊆all)
    (q:σ→O)(z a b:σ→ℝ)(W:σ→ℝ→ℂ)
    (hz:∀i∈all,0≤z i)(hq:∀i∈assigned,q i≠0)
    (hW:∀i∈assigned,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hret:∀i∈assigned,W i ((Ideal.absNorm (Ideal.span {q i}):ℝ)/Z^(z i))≠0)
    (hthreshold:(∏i∈assigned,b i)≤Z^η)
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H))
    (m r τ Pmax Smax κ:ℝ)(hD:D=r+assignedCenter all z-2*assignedCenter assigned z)
    (hr0:0≤Pmax)(hr:r≤Pmax)(hzS:assignedCenter all z≤Smax)(hm1:1≤m)(hτ0:0≤τ)(hκ:8*η+τ≤κ)
    (hcut:radialCenter m H θ D B≤4*η+τ)
    (hclip:max 0 (D-B-v)-(D-B-v)≤3*η):
    let N:=max 0 (D-B-v)
    let V:=θ+v+2*η
    let M:=θ+H+2*η
    let j:=assignedElement assigned q
    j*primaryGenerator t≠0 ∧ 0≤N ∧ 0≤V ∧ 0≤M ∧
    0≤fullPunctureWidth Z t j ∧
    ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    InitState Pmax Smax κ N V M (fullPunctureWidth Z t j) (assignedCenter (all\assigned) z+η) := by
  dsimp only
  have hretained:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hP: -2*η≤B-θ:=by
    have hn:=(nonempty_radius p hp (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ)
      Z (B-θ) η hZ ⟨t,hretained⟩
      (retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
        (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZ)
        (hψ 0) (hψ 1) (hhi 0) hdlo hdiv)).2
    linarith
  have hreg:=assigned_register all assigned hassigned z hz
  have hj:assignedElement assigned q≠0:=Finset.prod_ne_zero_iff.mpr hq
  have hnj:=assigned_norm_power assigned q z a b W Z η (zero_lt_one.trans hZ) hW hret hthreshold
  obtain ⟨hm,hQ0,hnorm,hQ⟩:=retained_full_puncture p hp hpr S ψ D v H
    (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (assignedCenter assigned z) hZ
    (hψ 0) (hψ 1) (hhi 0) hdlo hdiv (assignedElement assigned q) hj hnj ht
  obtain ⟨x,hx,hxt⟩:=Finset.mem_image.mp ht
  obtain ⟨hV,hM⟩:=live_widths_nonnegative p hp hpr S ψ lo hi hψ Z D B v θ H η hZ hhi
    hx (hf x (Finset.mem_filter.mp hx).1)
  have hGz : assignedCenter assigned z ≤ assignedCenter all z :=
    Finset.sum_le_sum_of_subset_of_nonneg hassigned (fun i hi _ => hz i hi)
  have hstate := initState_of_window Pmax Smax κ m r (assignedCenter all z)
    (assignedCenter assigned z) B θ v H η τ (fullPunctureWidth Z t (assignedElement assigned q))
    hr hzS hm1 hreg.1 hGz hη hτ0 hr0 hκ hP hV hQ (by rw [hD] at hclip; exact hclip)
    (by rw [hD] at hcut; exact hcut)
  have hlive : assignedCenter all z - assignedCenter assigned z =
      assignedCenter (all\assigned) z := by
    unfold assignedCenter
    rw [Finset.sum_sdiff_eq_sub hassigned]
  rw [hlive, show r+assignedCenter all z-2*assignedCenter assigned z-B-v = D-B-v by
    rw [hD]] at hstate
  exact ⟨hm,le_max_left _ _,hV,hM,hQ0,hnorm,hstate⟩

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.window_initState
