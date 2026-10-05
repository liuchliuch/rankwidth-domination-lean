import RankwidthDomination.TargetMetadataExecution

/-! Fixed-constant family extensions and ordinary-order caterpillar witnesses.
The constants describe a fixed target problem, never a source-dependent table. -/
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination.TargetMetadataMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding WitnessMachine WitnessDimensions

/-- Constant-size code for adding a fixed number of unary symbols. -/
def pushConstant (r : Register) : (n : ℕ) → Program Register (ClearLabels n)
  | 0 => ⟨(),fun _ => .halt⟩
  | n+1 => seq (pushBit r true) (pushConstant r n)

theorem pushConstant_exec (r : Register) (n : ℕ) (s : Register → List Bool) :
    Exec (pushConstant r n) ⟨some (pushConstant r n).entry,s⟩ (2*n+1)
      ⟨none,Function.update s r (unary n++s r)⟩ := by
  induction n generalizing s with
  | zero => simpa [unary] using (Exec.succ (p:=pushConstant r 0) (c:=⟨some (),s⟩) rfl (Exec.refl _))
  | succ n ih =>
    have hp := pushBit_exec r true s
    have hi := ih (Function.update s r (true::s r))
    have he : Function.update (Function.update s r (true::s r)) r
        (unary n++(Function.update s r (true::s r)) r) =
        Function.update s r (unary (n+1)++s r) := by
      simp [unary,List.replicate_succ',List.append_assoc]
    rw [he] at hi
    have hh := seq_exec hp hi
    convert hh using 1 <;> try rfl
    omega

def addFixedCounts (extraVertices extraTarget : ℕ) :=
  seq (pushConstant Register.vertices extraVertices) (pushConstant .target extraTarget)

def familyCounts (extraVertices extraTarget k m : ℕ) : Register → ℕ :=
  Function.update (Function.update (finalCounts k m) .vertices (vertexCount k m+extraVertices))
    .target (targetBudget k m+extraTarget)

theorem addFixedCounts_exec (extraVertices extraTarget k m : ℕ) :
    Exec (addFixedCounts extraVertices extraTarget)
      ⟨some (addFixedCounts extraVertices extraTarget).entry,numericState (finalCounts k m)⟩
      (2*extraVertices+2*extraTarget+2)
      ⟨none,numericState (familyCounts extraVertices extraTarget k m)⟩ := by
  let s := numericState (finalCounts k m)
  let t := Function.update s Register.vertices (unary (vertexCount k m+extraVertices))
  have h₁ := pushConstant_exec Register.vertices extraVertices s
  have he1 : Function.update s Register.vertices (unary extraVertices++s Register.vertices) = t := by
    funext r; cases r <;> simp [t,s,numericState,finalCounts,unary,Function.update,Nat.add_comm]
  rw [he1] at h₁
  have h₂ := pushConstant_exec Register.target extraTarget t
  have he2 : Function.update t Register.target (unary extraTarget++t Register.target) =
      numericState (familyCounts extraVertices extraTarget k m) := by
    funext r; cases r <;> simp [t,s,numericState,familyCounts,finalCounts,targetBudget,
      unary,Function.update,Nat.add_comm]
  rw [he2] at h₂
  have hh := seq_exec h₁ h₂
  convert hh using 1 <;> try rfl
  omega

/-- Work tapes are genuinely empty before witness generation; dimension
registers remain arbitrary concrete unary words. -/
structure Clean (s : Register → List Bool) : Prop where
  input : s .input = []
  remaining : s .remaining = []
  index : s .index = []
  output : s .output = []
  scratch : s .scratch = []
  temporary : s .temporary = []
  temporary2 : s .temporary2 = []
  length : s .length = []
  blocks : s .blocks = []

def orderPostlude := seq headerProgram (seq orderRaw prependHeader)
def nonePostlude := seq headerProgram (seq (pushBit Register.input false)
  (seq (pushBit Register.input false) prependHeader))
def pathPostlude := seq headerProgram (seq (blockProgram Register.vertices)
  (seq finishTreeRaw prependHeader))

def pathWord (n : ℕ) : List Bool := blockWords n 0

def orderPostState (s : Register → List Bool) (n d : ℕ) : Register → List Bool :=
  Function.update (headerState s n d) .input (orderCertificate n)
def nonePostState (s : Register → List Bool) (n d : ℕ) : Register → List Bool :=
  Function.update (headerState s n d) .input [false,false]
def pathPostState (s : Register → List Bool) (n d : ℕ) : Register → List Bool :=
  finishState (indexState (headerState s n d) 0 n (pathWord n).reverse) (pathWord n)

def orderPostTime (s : Register → List Bool) (n d : ℕ) : ℕ :=
  (16*n+16*d+44) + (orderTime n+3*n+2) + prependTime (orderPostState s n d) n d (orderCertificate n)
def nonePostTime (s : Register → List Bool) (n d : ℕ) : ℕ :=
  (16*n+16*d+44)+4+prependTime (nonePostState s n d) n d [false,false]
def pathPostTime (s : Register → List Bool) (n d : ℕ) : ℕ :=
  (16*n+16*d+44)+blockCost n 0+(9*(pathWord n).length+14)+
    prependTime (pathPostState s n d) n d (treeCertificateWord (pathWord n))

theorem orderPostlude_exec (s : Register → List Bool) (n d : ℕ) (hc : Clean s)
    (hn : s .vertices = unary n) (hd : s .target = unary d) :
    Exec orderPostlude ⟨some orderPostlude.entry,s⟩ (orderPostTime s n d)
      ⟨none,ioStacks Register.input (metadata n d (orderCertificate n))⟩ := by
  have hh := headerProgram_exec s n d hn hd hc.scratch hc.length hc.temporary2
  have ho := orderRaw_exec (headerState s n d) n
    (by simp [headerState,hn]) (by simp [headerState,hc.input]) (by simp [headerState,hc.remaining])
    (by simp [headerState,hc.index]) (by simp [headerState,hc.output]) (by simp [headerState,hc.scratch])
  have ha := prependHeader_exec (orderPostState s n d) n d (orderCertificate n)
    (by simp [orderPostState,headerState]) (by simp [orderPostState])
  have ht : orderPostTime s n d = (16*n+16*d+44) +
      ((orderTime n+3*n+2)+prependTime (orderPostState s n d) n d (orderCertificate n)) := by
    unfold orderPostTime; omega
  rw [ht]
  exact seq_exec hh (seq_exec ho ha)

theorem nonePostlude_exec (s : Register → List Bool) (n d : ℕ) (hc : Clean s)
    (hn : s .vertices = unary n) (hd : s .target = unary d) :
    Exec nonePostlude ⟨some nonePostlude.entry,s⟩ (nonePostTime s n d)
      ⟨none,ioStacks Register.input (metadata n d [false,false])⟩ := by
  have hh := headerProgram_exec s n d hn hd hc.scratch hc.length hc.temporary2
  have h₁ := pushBit_exec Register.input false (headerState s n d)
  have hi : headerState s n d Register.input = [] := by simp [headerState,hc.input]
  simp only [hi] at h₁
  have h₂ := pushBit_exec Register.input false (Function.update (headerState s n d) Register.input [false])
  simp only [Function.update_self,Function.update_idem] at h₂
  have ha := prependHeader_exec (nonePostState s n d) n d [false,false]
    (by simp [nonePostState,headerState]) (by simp [nonePostState])
  have ht : nonePostTime s n d = (16*n+16*d+44) +
      (2+(2+prependTime (nonePostState s n d) n d [false,false])) := by unfold nonePostTime; omega
  rw [ht]
  exact seq_exec hh (seq_exec h₁ (seq_exec h₂ ha))

theorem pathPostlude_exec (s : Register → List Bool) (n d : ℕ) (hc : Clean s)
    (hn : s .vertices = unary n) (hd : s .target = unary d) (hnpos : 0 < n) :
    Exec pathPostlude ⟨some pathPostlude.entry,s⟩ (pathPostTime s n d)
      ⟨none,ioStacks Register.input (metadata n d (treeCertificateWord (pathWord n)))⟩ := by
  have hh := headerProgram_exec s n d hn hd hc.scratch hc.length hc.temporary2
  have hs0 : indexState (headerState s n d) 0 0 [] = headerState s n d := by
    funext r; cases r <;> simp [indexState,headerState,Function.update,unary,hc.remaining,hc.index,hc.output]
  have hb := blockProgram_exec Register.vertices (by decide) (by decide) (by decide)
    (by decide) (by decide) (headerState s n d) n 0 hnpos (by simp [headerState,hn])
    (by simp [headerState,hc.scratch]) (by simp [headerState,hc.temporary]) []
  simp only [hs0,Nat.zero_add,List.append_nil] at hb
  have hf := finishTreeRaw_exec (indexState (headerState s n d) 0 n (pathWord n).reverse) (pathWord n)
    (by simp [indexState,headerState,hc.input]) (by simp)
    (by simp [indexState,headerState,hc.temporary]) (by simp [indexState,headerState,hc.length])
  have ha := prependHeader_exec (pathPostState s n d) n d (treeCertificateWord (pathWord n))
    (by simp [pathPostState,finishState,indexState,headerState]) (by simp [pathPostState,finishState])
  have ht : pathPostTime s n d = (16*n+16*d+44) +
      (blockCost n 0 + ((9*(pathWord n).length+14)+prependTime (pathPostState s n d) n d
        (treeCertificateWord (pathWord n)))) := by unfold pathPostTime; omega
  rw [ht]
  exact seq_exec hh (seq_exec hb (seq_exec hf ha))

/-- Fixed constants cover bipartite (+3,+1) and reservoir (+3b,+b) variants. -/
def familyPrelude (extraVertices extraTarget : ℕ) := seq parseDimensions
  (seq prepareDimensions (addFixedCounts extraVertices extraTarget))

def familyPreludeTime (v t k m : ℕ) : ℕ := 2*k+2*m+4+dimensionsTime k m+(2*v+2*t+2)

def familyPrepared (v t k m : ℕ) : Register → List Bool := numericState (familyCounts v t k m)

theorem familyPrelude_exec (v t k m : ℕ) :
    Exec (familyPrelude v t) ⟨some (familyPrelude v t).entry,ioStacks Register.input (dimensionInput k m)⟩
      (familyPreludeTime v t k m) ⟨none,familyPrepared v t k m⟩ := by
  have h := seq_exec (parseDimensions_exec k m)
    (seq_exec (prepareDimensions_exec k m) (addFixedCounts_exec v t k m))
  have ht : familyPreludeTime v t k m = (2*k+2*m+4)+(dimensionsTime k m+(2*v+2*t+2)) := by
    unfold familyPreludeTime; omega
  rw [ht]
  exact h

theorem familyPrepared_clean (v t k m : ℕ) : Clean (familyPrepared v t k m) := by
  constructor <;> simp [familyPrepared,familyCounts,numericState,finalCounts,unary]

def familyOrderProgram (v t : ℕ) := seq (familyPrelude v t) orderPostlude
def familyNoneProgram (v t : ℕ) := seq (familyPrelude v t) nonePostlude
def familyPathProgram (v t : ℕ) := seq (familyPrelude v t) pathPostlude

def familyOrderTime (v t k m : ℕ) := familyPreludeTime v t k m +
  orderPostTime (familyPrepared v t k m) (vertexCount k m+v) (targetBudget k m+t)
def familyNoneTime (v t k m : ℕ) := familyPreludeTime v t k m +
  nonePostTime (familyPrepared v t k m) (vertexCount k m+v) (targetBudget k m+t)
def familyPathTime (v t k m : ℕ) := familyPreludeTime v t k m +
  pathPostTime (familyPrepared v t k m) (vertexCount k m+v) (targetBudget k m+t)

theorem familyOrderProgram_exec (v t k m : ℕ) :
    Exec (familyOrderProgram v t)
      ⟨some (familyOrderProgram v t).entry,ioStacks Register.input (dimensionInput k m)⟩
      (familyOrderTime v t k m) ⟨none,ioStacks Register.input
        (metadata (vertexCount k m+v) (targetBudget k m+t) (orderCertificate (vertexCount k m+v)))⟩ := by
  exact seq_exec (familyPrelude_exec v t k m)
    (orderPostlude_exec _ _ _ (familyPrepared_clean v t k m)
      (by simp [familyPrepared,numericState,familyCounts])
      (by simp [familyPrepared,numericState,familyCounts]))

theorem familyNoneProgram_exec (v t k m : ℕ) :
    Exec (familyNoneProgram v t)
      ⟨some (familyNoneProgram v t).entry,ioStacks Register.input (dimensionInput k m)⟩
      (familyNoneTime v t k m) ⟨none,ioStacks Register.input
        (metadata (vertexCount k m+v) (targetBudget k m+t) [false,false])⟩ := by
  exact seq_exec (familyPrelude_exec v t k m)
    (nonePostlude_exec _ _ _ (familyPrepared_clean v t k m)
      (by simp [familyPrepared,numericState,familyCounts])
      (by simp [familyPrepared,numericState,familyCounts]))

theorem familyPathProgram_exec (v t k m : ℕ) :
    Exec (familyPathProgram v t)
      ⟨some (familyPathProgram v t).entry,ioStacks Register.input (dimensionInput k m)⟩
      (familyPathTime v t k m) ⟨none,ioStacks Register.input
        (metadata (vertexCount k m+v) (targetBudget k m+t)
          (treeCertificateWord (pathWord (vertexCount k m+v))))⟩ := by
  apply seq_exec (familyPrelude_exec v t k m)
  apply pathPostlude_exec _ _ _ (familyPrepared_clean v t k m)
    (by simp [familyPrepared,numericState,familyCounts])
    (by simp [familyPrepared,numericState,familyCounts])
  unfold vertexCount layerSize
  positivity

end RankwidthDomination.TargetMetadataMachine
