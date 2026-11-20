/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine fixed and all-response regular suppliers share one finite
early bank before every live source, height and positive root fee. -/
import Candidate.C092.transport.ActualStageFrameBudgetNativeBank
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonProfile CenteredMomentDetectorPlainFiberSource
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.Cycle092.RegularFramePhysicalReturn
open QRH.Cycle092.PairedRetainedBudget
open QRH.Cycle092.RegularPhysicalClassBudget QRH.Cycle092.WholeSlot
open QRH.Cycle090 QRH.Cycle092.Source QRH.SourceCertificate
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- Only finite early metadata; all scale-dependent physical assertions
are the literal native packets in At below. -/
structure NativePhysicalBank (N:ℕ) where
  jf:Fin (N+1)→ℕ
  jr:Fin (N+1)→ℕ
  Sf:Fin (N+1)→Finset (ℕ×ℕ)
  Sr:Fin (N+1)→Finset (ℕ×ℕ)
  Cr:Fin (N+1)→ℝ
  Cgr:Fin (N+1)→ℝ
  Cf:Fin (N+1)→ℝ
  Cgf:Fin (N+1)→ℝ
  Cfixed:ℝ
  Cregular:ℝ
  fixed_pos:0 < Cfixed
  regular_pos:0 < Cregular
  regular_data:∀k,0 < Cr k ∧ 0  ≤  Cgr k
  fixed_data:∀k,(0,0)∈Sf k ∧ 0  ≤  Cgf k ∧ 0 < Cf k

namespace NativePhysicalBank
variable {N:ℕ}
def J(b:NativePhysicalBank N):ℕ:=commonJ (mergeJ b.jf b.jr)
def degree(b:NativePhysicalBank N):ℕ:=commonDegree (mergeJ b.jf b.jr) (mergeDegree b.jf b.jr)
def controls(b:NativePhysicalBank N):Finset (ℕ×ℕ):=commonControls (mergeControls b.Sf b.Sr)
def totalFee(b:NativePhysicalBank N):ℝ:=b.Cfixed+b.Cregular

theorem mem_controls (b:NativePhysicalBank N):(0,0)∈b.controls:=
  (finite_bank_parameters N (mergeJ b.jf b.jr) (mergeDegree b.jf b.jr) (mergeControls b.Sf b.Sr)).1

theorem regular_J_le (b:NativePhysicalBank N)(k:Fin (N+1)):b.jr k  ≤  b.J:=by
  simpa [J,mergeJ] using
    ((finite_bank_parameters N (mergeJ b.jf b.jr) (mergeDegree b.jf b.jr) (mergeControls b.Sf b.Sr)).2 (k,false)).1

def Fee(b:NativePhysicalBank N):Prop:=
  ∀k:Fin (N+1),∀{L mesh Z:ℝ}{θ:GData L},θ.a=1/4 →
    ∀(η:Character)(rs:GSrc θ mesh Z)(p:Profiles (1/4) (9/4))(t₁ t₂ height:ℝ),
    0  ≤  height → rs.Vf  ≤  height → rs.t=t₁ → rs.t₁=t₁/(2*Real.pi) → rs.t₂=t₂/(2*Real.pi) →
    rs.W₁=p.profile 0 → rs.W₂=p.profile 1 →
    classLambda 1 (b.Cgr k) 1 (b.Cr k*gAmp L θ mesh η Z rs (b.jr k) (b.Sr k)) θ.a (b.jr k)  ≤ 
      b.Cregular*((p.control b.controls)^2*(1+|t₁|+|t₂|+height)^b.degree)

def At(b:NativePhysicalBank N)(θ:Fin (N+1)→GData 3)(η ω₁ ω₂:Character)
    (Q:Id)(mesh δ n y Kslot Z:ℝ)(hδ:0 < δ):Prop:=
  ∀k:Fin (N+1),
    FixedGlobalAt (θ k) η ω₁ ω₂ mesh δ δ δ (b.jf k) (b.Sf k) (b.Cgf k) Q (b.Cf k) Z
      b.J b.degree b.controls b.Cfixed Kslot ∧
    (k.val=0 → PartWithFeeAt (θ k) mesh η ω₁ ω₂ 0 (19/10) δ δ (δ+δ)
      (b.jr k) (b.Sr k) (b.Cr k) (b.Cgr k) (exhaustedPrice (θ k) mesh δ hδ.le)
      (exhaustedCaps (θ k) mesh) Z) ∧
    (k.val≠0 → PartAt (θ k) mesh η ω₁ ω₂ 0 (19/10) δ δ
      (b.jr k) (b.Sr k) (b.Cr k) (b.Cgr k) (filledPrice (θ k) mesh) (filledCaps (θ k) mesh n y) Z)
end NativePhysicalBank

theorem actual_physical_bank (δ:ℝ) (hδ:0   <   δ) :
    ∃meshMax:ℝ,0   <   meshMax ∧ ∀mesh:ℝ,0   <   mesh → mesh   ≤   meshMax →
    ∀(N:ℕ)(rayM:Id)[NeZero rayM](Hr:Subgroup (O⧸rayM)ˣ)
      (hHr:RayOrthogonality.globalUnits rayM    ≤    Hr)
      (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
      (base:Character)(Q:Id)(hQ:Q    ≤    rayM)(hQ0:Q≠0)(hQt:Q≠⊤)
      (hQ72:Q    ≤    Ideal.span {(72:O)})(hQbase:Q    ≤    base.modulus),
    let θ:=fun k:Fin (N+1)=>frameData N k.val rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase
    ∀(bPhi:ℝ)(hbPhi:2  ≤  bPhi)(hPhi:Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi)
      (hβ:(51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
      (n y:ℝ)(hy₀:sourceY0   ≤   y)(hy₁:y   ≤   sourceY)(hn:y   ≤   n)
      (η ω₁ ω₂:Character)(hQ₁:Q   ≤   ω₁.modulus)(hQ₂:Q   ≤   ω₂.modulus)
      (Dp:Fin (N+1)→ℕ)(Sp:Fin (N+1)→Finset (ℕ×ℕ))(Cp:Fin (N+1)→ℝ),
      (∀k,0   <   Cp k) →
      (∀k,∀j:DictIdx,∀ᶠ Z:ℝ in atTop,
        OrderedP2At (Fin k.val) rayM Hr hHr W n y mesh Z
          (anchors η j) base ω₁ ω₂ Q (Dp k) (Sp k) (Cp k)) →
    ∀Kslot:ℝ,1   ≤   Kslot →
    ∃bank:NativePhysicalBank N,bank.Fee ∧ ∀ᶠZ:ℝ in atTop,
      bank.At θ η ω₁ ω₂ Q mesh δ n y Kslot Z hδ := by
  obtain ⟨meshMax,hmmax,hproduce⟩:=actual_native_bank δ hδ
  refine ⟨meshMax,hmmax,?_⟩
  intro mesh hm hmm N rayM inst Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase θ
    bPhi hbPhi hPhi hβ n y hy₀ hy₁ hn η ω₁ ω₂ hQ₁ hQ₂ Dp Sp Cp hCp hP2 Kslot hKslot
  obtain ⟨jr,Sr,Cr,Cgr,jf,Sf,Cgf,Cf,Cfixed,Cregular,hCfixed,hCregular,h00,hreg,hfix,hscale,hfee⟩:=
    hproduce mesh hm hmm N rayM Hr hHr W hW hWs base Q hQ hQ0 hQt hQ72 hQbase
      bPhi hbPhi hPhi hβ n y hy₀ hy₁ hn η ω₁ ω₂ hQ₁ hQ₂ Dp Sp Cp hCp hP2 Kslot hKslot
  let bank:NativePhysicalBank N:=⟨jf,jr,Sf,Sr,Cr,Cgr,Cf,Cgf,Cfixed,Cregular,hCfixed,hCregular,hreg,hfix⟩
  exact ⟨bank,hfee,hscale⟩

#print axioms actual_physical_bank
#print axioms NativePhysicalBank.regular_J_le
end
end QRH.Cycle092.ActualStageFrameBudget
