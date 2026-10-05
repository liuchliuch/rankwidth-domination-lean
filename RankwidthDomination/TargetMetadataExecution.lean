import RankwidthDomination.TargetMetadataMachine

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 100000
namespace RankwidthDomination.TargetMetadataMachine
open Complexity PaddingMachine PaddingPipeline Padding.BinaryEncoding WitnessMachine WitnessDimensions

theorem orderRaw_exec (s : Register → List Bool) (n : ℕ)
    (hn : s .vertices = unary n) (hi : s .input = []) (hr : s .remaining = [])
    (hindex : s .index = []) (ho : s .output = []) (hs : s .scratch = []) :
    Exec orderRaw ⟨some orderRaw.entry,s⟩ (orderTime n+3*n+2)
      ⟨none,Function.update s Register.input (orderCertificate n)⟩ := by
  have h₀ := duplicateReverse_exec_general Register.vertices .remaining .scratch
    (by decide) (by decide) (by decide) s hs
  have hp : Function.update s Register.remaining ((s Register.vertices).reverse++s Register.remaining) =
      indexState s n 0 [] := by
    funext r; cases r <;> simp [indexState,hn,hr,hindex,ho,unary,Function.update]
  rw [hp] at h₀
  simp only [hn,unary,List.length_replicate] at h₀
  have h₁ := pushBit_exec Register.output false (indexState s n 0 [])
  simp only [indexState_output,update_indexState_output] at h₁
  have h₂ := pushBit_exec Register.output true (indexState s n 0 [false])
  simp only [indexState_output,update_indexState_output] at h₂
  have h₃ := emitUnary_exec_general Register.remaining .output .scratch (by decide) (by decide)
    (by decide) (indexState s n 0 [true,false]) n (by simp) (by simp [hs])
  simp only [indexState_output,update_indexState_output] at h₃
  have h₄ := indexLoop_exec s hs n 0 ((natCode n).reverse++[true,false])
  have hoeq : (indexWords n 0).reverse ++ ((natCode n).reverse++[true,false]) =
      (orderCertificate n).reverse := by simp [orderCertificate,List.reverse_append,List.append_assoc]
  simp only [Nat.zero_add,hoeq] at h₄
  have h₅ := clear_exec_general Register.index (indexState s 0 n (orderCertificate n).reverse)
  have hcl : Function.update (indexState s 0 n (orderCertificate n).reverse) Register.index [] =
      indexState s 0 0 (orderCertificate n).reverse := by
    simpa only [unary,List.replicate_zero] using update_indexState_index s 0 n 0 (orderCertificate n).reverse
  simp only [indexState_index,unary,List.length_replicate,hcl] at h₅
  have h₆ := transfer_exec_general Register.output .input (by decide)
    (indexState s 0 0 (orderCertificate n).reverse)
  have hfinal : Function.update (Function.update (indexState s 0 0 (orderCertificate n).reverse)
      Register.output []) Register.input
      (((indexState s 0 0 (orderCertificate n).reverse) .output).reverse ++
        indexState s 0 0 (orderCertificate n).reverse .input) =
      Function.update s Register.input (orderCertificate n) := by
    funext r; cases r <;> simp [indexState,unary,Function.update,hi,hr,hindex,ho]
  rw [hfinal] at h₆
  simp only [indexState_output,List.length_reverse] at h₆
  have hall := seq_exec h₀ (seq_exec h₁ (seq_exec h₂ (seq_exec h₃ (seq_exec h₄ (seq_exec h₅ h₆)))))
  have htime : orderTime n+3*n+2 = (5*n+4)+(2+(2+((5*n+6)+
      ((indexCost n 0+n+2)+((n+2)+(2*(orderCertificate n).length+2)))))) := by
    unfold orderTime; omega
  rw [htime]
  exact hall

def targetBudget (k m : ℕ) : ℕ := (m+1)*k

def prepared (k m : ℕ) : Register → List Bool := numericState (finalCounts k m)

def headerPrepared (k m : ℕ) : Register → List Bool :=
  headerState (prepared k m) (vertexCount k m) (targetBudget k m)

def preludeTime (k m : ℕ) : ℕ :=
  2*k+2*m+4 + dimensionsTime k m + (16*vertexCount k m+16*targetBudget k m+44)

theorem metadataPrelude_exec (k m : ℕ) :
    Exec metadataPrelude ⟨some metadataPrelude.entry,ioStacks Register.input (dimensionInput k m)⟩
      (preludeTime k m) ⟨none,headerPrepared k m⟩ := by
  have hp := parseDimensions_exec k m
  have hd := prepareDimensions_exec k m
  have hh := headerProgram_exec (prepared k m) (vertexCount k m) (targetBudget k m)
    (by simp [prepared,numericState,finalCounts])
    (by simp [prepared,numericState,finalCounts,targetBudget])
    (by simp [prepared,numericState,finalCounts,unary])
    (by simp [prepared,numericState,finalCounts,unary])
    (by simp [prepared,numericState,finalCounts,unary])
  have ht : preludeTime k m = (2*k+2*m+4) +
      (dimensionsTime k m + (16*vertexCount k m+16*targetBudget k m+44)) := by
    unfold preludeTime; omega
  rw [ht]
  exact seq_exec hp (seq_exec hd hh)

def treeBodyState (k m : ℕ) : Register → List Bool :=
  indexState (headerPrepared k m) 0 (vertexCount k m) (treeOutputWord k m).reverse

def treeReadyState (k m : ℕ) : Register → List Bool :=
  finishState (treeBodyState k m) (treeOutputWord k m)

def orderReadyState (k m : ℕ) : Register → List Bool :=
  Function.update (headerPrepared k m) .input (orderCertificate (vertexCount k m))

def noneReadyState (k m : ℕ) : Register → List Bool :=
  Function.update (headerPrepared k m) .input [false,false]

def treeMetadataTime (k m : ℕ) : ℕ :=
  preludeTime k m + treeBodyCost m (layerSize k) (checkerSize k) +
    (9*(treeOutputWord k m).length+14) + prependTime (treeReadyState k m)
      (vertexCount k m) (targetBudget k m) (treeCertificateWord (treeOutputWord k m))

def orderMetadataTime (k m : ℕ) : ℕ :=
  preludeTime k m + (orderTime (vertexCount k m)+3*vertexCount k m+2) +
    prependTime (orderReadyState k m) (vertexCount k m) (targetBudget k m)
      (orderCertificate (vertexCount k m))

def noneMetadataTime (k m : ℕ) : ℕ :=
  preludeTime k m+4 + prependTime (noneReadyState k m)
    (vertexCount k m) (targetBudget k m) [false,false]

theorem treeMetadataProgram_exec (k m : ℕ) (hk : 0 < k) :
    Exec treeMetadataProgram
      ⟨some treeMetadataProgram.entry,ioStacks Register.input (dimensionInput k m)⟩
      (treeMetadataTime k m) ⟨none,ioStacks Register.input
        (metadata (vertexCount k m) (targetBudget k m) (treeCertificateWord (treeOutputWord k m)))⟩ := by
  have hp := metadataPrelude_exec k m
  let H := headerPrepared k m
  have hs : indexState H 0 0 [] = H := by
    funext r; cases r <;> simp [H,headerPrepared,headerState,prepared,numericState,
      finalCounts,indexState,unary,Function.update]
  have hb := treeBody_exec H m (layerSize k) (checkerSize k) (layerSize_pos k) (checkerSize_pos hk)
    (by simp [H,headerPrepared,headerState,prepared,numericState,finalCounts])
    (by simp [H,headerPrepared,headerState,prepared,numericState,finalCounts])
    (by simp [H,headerPrepared,headerState,prepared,numericState,finalCounts])
    (by simp [H,headerPrepared,headerState,prepared,numericState,finalCounts,unary])
    (by simp [H,headerPrepared,headerState,prepared,numericState,finalCounts,unary])
    (by simp [H,headerPrepared,headerState,prepared,numericState,finalCounts,unary]) []
  have hN : m*(layerSize k+checkerSize k)+layerSize k = vertexCount k m := by
    unfold vertexCount; ring
  simp only [hs,hN,List.append_nil] at hb
  have hf := finishTreeRaw_exec (treeBodyState k m) (treeOutputWord k m)
    (by simp [treeBodyState,indexState,headerPrepared,headerState,prepared,numericState,finalCounts,unary])
    (by simp [treeBodyState])
    (by simp [treeBodyState,indexState,headerPrepared,headerState,prepared,numericState,finalCounts,unary])
    (by simp [treeBodyState,indexState,headerPrepared,headerState,prepared,numericState,finalCounts,unary])
  have ha := prependHeader_exec (treeReadyState k m) (vertexCount k m) (targetBudget k m)
    (treeCertificateWord (treeOutputWord k m))
    (by simp [treeReadyState,finishState,treeBodyState,indexState,headerPrepared,headerState])
    (by simp [treeReadyState,finishState])
  have ht : treeMetadataTime k m = preludeTime k m +
      (treeBodyCost m (layerSize k) (checkerSize k) + ((9*(treeOutputWord k m).length+14) +
        prependTime (treeReadyState k m) (vertexCount k m) (targetBudget k m)
          (treeCertificateWord (treeOutputWord k m)))) := by unfold treeMetadataTime; omega
  rw [ht]
  exact seq_exec hp (seq_exec hb (seq_exec hf ha))

theorem orderMetadataProgram_exec (k m : ℕ) :
    Exec orderMetadataProgram
      ⟨some orderMetadataProgram.entry,ioStacks Register.input (dimensionInput k m)⟩
      (orderMetadataTime k m) ⟨none,ioStacks Register.input
        (metadata (vertexCount k m) (targetBudget k m) (orderCertificate (vertexCount k m)))⟩ := by
  have hp := metadataPrelude_exec k m
  have ho := orderRaw_exec (headerPrepared k m) (vertexCount k m)
    (by simp [headerPrepared,headerState,prepared,numericState,finalCounts])
    (by simp [headerPrepared,headerState,prepared,numericState,finalCounts,unary])
    (by simp [headerPrepared,headerState,prepared,numericState,finalCounts,unary])
    (by simp [headerPrepared,headerState,prepared,numericState,finalCounts,unary])
    (by simp [headerPrepared,headerState,prepared,numericState,finalCounts,unary])
    (by simp [headerPrepared,headerState,prepared,numericState,finalCounts,unary])
  have ha := prependHeader_exec (orderReadyState k m) (vertexCount k m) (targetBudget k m)
    (orderCertificate (vertexCount k m))
    (by simp [orderReadyState,headerPrepared,headerState]) (by simp [orderReadyState])
  have ht : orderMetadataTime k m = preludeTime k m +
      ((orderTime (vertexCount k m)+3*vertexCount k m+2) +
        prependTime (orderReadyState k m) (vertexCount k m) (targetBudget k m)
          (orderCertificate (vertexCount k m))) := by unfold orderMetadataTime; omega
  rw [ht]
  exact seq_exec hp (seq_exec ho ha)

theorem noneMetadataProgram_exec (k m : ℕ) :
    Exec noneMetadataProgram
      ⟨some noneMetadataProgram.entry,ioStacks Register.input (dimensionInput k m)⟩
      (noneMetadataTime k m) ⟨none,ioStacks Register.input
        (metadata (vertexCount k m) (targetBudget k m) [false,false])⟩ := by
  have hp := metadataPrelude_exec k m
  have h₁ := pushBit_exec Register.input false (headerPrepared k m)
  have hi : headerPrepared k m Register.input = [] := by
    simp [headerPrepared,headerState,prepared,numericState,finalCounts,unary]
  simp only [hi] at h₁
  have h₂ := pushBit_exec Register.input false (Function.update (headerPrepared k m) Register.input [false])
  simp only [Function.update_self,Function.update_idem] at h₂
  have ha := prependHeader_exec (noneReadyState k m) (vertexCount k m) (targetBudget k m)
    [false,false] (by simp [noneReadyState,headerPrepared,headerState]) (by simp [noneReadyState])
  have ht : noneMetadataTime k m = preludeTime k m +
      (2+(2+prependTime (noneReadyState k m) (vertexCount k m) (targetBudget k m) [false,false])) := by
    unfold noneMetadataTime; omega
  rw [ht]
  exact seq_exec hp (seq_exec h₁ (seq_exec h₂ ha))

end RankwidthDomination.TargetMetadataMachine
