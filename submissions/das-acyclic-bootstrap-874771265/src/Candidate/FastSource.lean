/- Kernel-checked staging; Subhanjan Das, AI-assisted with OpenAI Codex.
Derived from Collet SourceFormulas, Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceFormulas
set_option autoImplicit false
set_option maxHeartbeats 0
namespace Das.QRH.FastSource
open Record1252270103Finite
def scalarFast (n low : Source) (b a t F : ℚ) (j : Fin 16) : ℚ :=
 let T := t+b
 let e := n.allowance
 let Lref := 49/100-(11243277/2500000)*b
 ![sourceDen n low,b-2*e,a,1/75-a,F-T/2-4*e,
 low.B*F-t-b-4*e,1-n.q*low.cap,
 n.lowFee-(n.q*low.B/low.L+n.q*low.cap+4)*e-10*e,
 a-20*e,Lref,1-Lref-1/2-(11243277/2500000)*b-10*e,
 5/6+(499/1000)*Lref-T-9*a-n.highFee,
 1-T-5*a-n.highFee,1-1/50-T-4*a-n.highFee,
 1-1/50-T-(9/2)*a-n.highFee,Lref-7*a-n.highFee] j

def weakFast (low : Source) (a t F : ℚ) : ℚ :=
 low.cap*F-(low.B*F-t)/low.L

def densityFast (n low : Source) (high : Option Source) (b a t0 F0 ν : ℚ) (j : Fin 9) : ℚ :=
 let T := t0+b
 let S := b-2*n.allowance
 let F := F0-n.allowance
 let fee := n.highFee
 let t := 15-6*ν
 let w := 5-6*ν
 let H := (a-ν*T)*t+(10-60*a)*ν
 let fixed := H+(ν*F/2-(1-ν)*b-fee)*t
 let core := H+((5/6)*F-(1-ν)*b-fee)*t-10*ν*F
 let tiny := H+(ν*(F-1/50)/2-(1-ν)*b-fee)*t-10*ν*(1/50)
 match high with
 | none =>
   let D2 := 115-54*ν
   let D3 := 185-138*ν
   ![H+3*ν*w*S-fee*t,
     H*D2+14*ν*w*S*t+2*ν*w*w*F-fee*t*D2,
     H*D3+16*ν*w*w*F-fee*t*D3,fixed,core,tiny,1,1,1] j
 | some h =>
   let D13 := h.L*t-10
   let D4 := 10+3*w
   let D23 := h.L*(10+3*w)-(10+2*w)
   ![H+3*ν*w*S-fee*t,
     H+(2*ν*w*S+ν*w*h.cap*F)-fee*t,
     H*D13+2*ν*w*(h.L-1)*S*t+ν*w*(h.B*t-10)*F-fee*t*D13,
     H*D4+ν*w*S*t+2*ν*w*w*F-fee*t*D4,
     H*D4+(2*ν*w*w+ν*w*h.cap*t)*F-fee*t*D4,
     H*D23+ν*w*(2*w*(h.L-1)+h.B*t-10)*F-fee*t*D23,
     fixed,core,tiny] j


def Endpoint (n low : Source) (high : Option Source) (b a t F : ℚ) : Prop :=
 (∀ j : Fin 16, 0<scalarFast n low b a t F j) ∧ 0≤weakFast low a t F ∧
 ∀ j : Fin 9, ∀ i : Fin 4, 0<cubicBernstein (fun ν => densityFast n low high b a t F ν j) n.q (3/4) i
instance (n low : Source) (high : Option Source) (b a t F : ℚ) : Decidable (Endpoint n low high b a t F) := by
 unfold Endpoint
 infer_instance

theorem endpoint_sound (n low : Source) (high : Option Source) (b a t F : ℚ)
 (ha : sourceA n low b=a) (ht : sourceT n b=t) (hf : sourceF n low b=F)
 (h : Endpoint n low high b a t F) :
 (∀ j : Fin 16, 0<scalarGate n low b j) ∧ 0≤weakCap n low b ∧
 ∀ j : Fin 9, ∀ i : Fin 4, 0<cubicBernstein (fun ν => densityGate n low high b ν j) n.q (3/4) i := by
 have hs : ∀j, scalarGate n low b j=scalarFast n low b a t F j := by
  intro j
  simp only [scalarGate,scalarFast,ha,ht,hf]
 have hw : weakCap n low b=weakFast low a t F := by
  simp only [weakCap,weakFast,ht,hf]
 have hd : ∀ν j, densityGate n low high b ν j=densityFast n low high b a t F ν j := by
  intro ν j
  simp only [densityGate,densityFast,ha,ht,hf]
  rfl
 simpa only [hs,hw,hd,Endpoint] using h

def Basic (n low : Source) (high : Option Source) (c : ℚ) : Prop :=
 0<n.B ∧ n.B≤1 ∧ 1<n.L ∧ 0≤n.cap ∧ n.cap<1 ∧
 1/2≤n.q ∧ n.q≤3/4 ∧ n.L<low.L ∧
 0≤c ∧ c≤n.cap ∧ c≤low.cap ∧
 (∀ h ∈ high, 22/23≤h.B ∧ h.B≤1 ∧ 1<h.L ∧ 0≤h.cap ∧ h.cap<1)
instance (n low : Source) (high : Option Source) (c : ℚ) : Decidable (Basic n low high c) := by
 unfold Basic
 infer_instance

theorem source_sound (n low : Source) (high : Option Source)
 (c a0 t0 f0 a1 t1 f1 : ℚ)
 (hc : crossing n low=c)
 (ha0 : sourceA n low c=a0) (ht0 : sourceT n c=t0) (hf0 : sourceF n low c=f0)
 (ha1 : sourceA n low n.cap=a1) (ht1 : sourceT n n.cap=t1) (hf1 : sourceF n low n.cap=f1)
 (hb : Basic n low high c)
 (he0 : Endpoint n low high c a0 t0 f0)
 (he1 : Endpoint n low high n.cap a1 t1 f1) : SourceValid n low high := by
 unfold SourceValid
 rw [hc]
 rcases hb with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
 refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,?_⟩
 intro b hb
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
 rcases hb with hb|hb
 · subst b
   exact endpoint_sound n low high c a0 t0 f0 ha0 ht0 hf0 he0
 · subst b
   exact endpoint_sound n low high n.cap a1 t1 f1 ha1 ht1 hf1 he1

def Data (n low : Source) (c a0 a1 : ℚ) : Prop :=
 crossing n low=c ∧ sourceA n low c=a0 ∧ sourceA n low n.cap=a1
instance (n low : Source) (c a0 a1 : ℚ) : Decidable (Data n low c a0 a1) := by
 unfold Data
 infer_instance

def Cert (n low : Source) (c a0 a1 : ℚ) : Prop :=
 Basic n low (some low) c ∧
 Endpoint n low (some low) c a0 (sourceT n c) (1-6*a0) ∧
 Endpoint n low (some low) n.cap a1 (sourceT n n.cap) (1-6*a1)
instance (n low : Source) (c a0 a1 : ℚ) : Decidable (Cert n low c a0 a1) := by
 unfold Cert
 infer_instance

theorem check {n low : Source} (c a0 a1 : ℚ)
 (hd : Data n low c a0 a1) (h : Cert n low c a0 a1) : SourceValid n low (some low) := by
 rcases hd with ⟨hc,ha0,ha1⟩
 rcases h with ⟨hb,h0,h1⟩
 exact source_sound n low (some low) c a0 (sourceT n c) (1-6*a0)
  a1 (sourceT n n.cap) (1-6*a1) hc ha0 rfl
  (by simp only [sourceF,ha0]) ha1 rfl (by simp only [sourceF,ha1]) hb h0 h1
end Das.QRH.FastSource
#print axioms Das.QRH.FastSource.source_sound
