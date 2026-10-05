import RankwidthDomination.MatrixSource
import RankwidthDomination.ExtendedTableEvaluation
import RankwidthDomination.GeneratorMachines

/-! Actual source-to-adjacency programs for bipartite and fixed sigma/rho families.
The source parser, dimension-only generator, sideband storage and serialized
matrix evaluator are all fixed finite programs with proved execution traces. -/
namespace RankwidthDomination
namespace ExtendedMatrixSource
open Complexity PaddingMachine PaddingPipeline
open GraphGenerator
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1000000
set_option maxHeartbeats 3000000

abbrev stackType {K L : Type} (_ : Program K L) : Type := K

def generation {K L : Type} [DecidableEq K] (p : Program K L) (gio : K) :=
  ProgramComposition.compose SourcePreprocessor.program (A .input)
    (Sideband.program p gio) (Sideband.I gio)

def generationIO {K L : Type} [DecidableEq K] (p : Program K L) (gio : K) :
    stackType (generation p gio) := ProgramComposition.firstIO (A .input)

def program {K L : Type} [DecidableEq K] (p : Program K L) (gio : K) :=
  ProgramComposition.compose (generation p gio) (generationIO p gio)
    ReductionMachine.serializedTableProgram ReductionMachine.Tape.source

def io {K L : Type} [DecidableEq K] (p : Program K L) (gio : K) : stackType (program p gio) :=
  ProgramComposition.firstIO (generationIO p gio)

abbrev denseLength := MatrixSource.denseLength

def bound (k m n : ℕ) (table : List Bool) (generatorBound : ℕ) : ℕ :=
  500*(k^2+m+2)^2 + generatorBound + 18*(k+m+2)+45*denseLength k m+
    16*table.length+n^2*(5*denseLength k m+10)+64

/-- Generic composition uses actual generator and evaluator traces, not runtime
or computability assumptions. The concrete family corollaries close both premises. -/
theorem program_exec {K L : Type} [DecidableEq K] (p : Program K L) (gio : K)
    {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (table output : List Bool) (n generatorBound : ℕ)
    (houtput : output.length=n^2)
    (hgenerator : ∃ tg ≤ generatorBound,
      Exec p ⟨some p.entry,ioStacks gio (GraphGenerator.dimensions k m)⟩ tg
        ⟨none,ioStacks gio table⟩)
    (hevaluator : Exec ReductionMachine.serializedTableProgram
      ⟨some ReductionMachine.serializedTableProgram.entry,
        ioStacks ReductionMachine.Tape.source
          (ReductionMachine.pairInput (ReductionMachine.denseInput (Padding.matrixCNF f hlen)) table)⟩
      (n^2*(5*denseLength k m+6)+8*denseLength k m+4*table.length+10)
      ⟨none,ioStacks ReductionMachine.Tape.source output⟩) :
    ∃ time ≤ bound k m n table generatorBound,
      Exec (program p gio)
        ⟨some (program p gio).entry,ioStacks (io p gio) (Padding.BinaryEncoding.formulaBits f)⟩ time
        ⟨none,ioStacks (io p gio) output⟩ := by
  let φ := Padding.matrixCNF f hlen
  let bits := ReductionMachine.denseInput φ
  let dims := GraphGenerator.dimensions k m
  obtain ⟨tp,htp,hp⟩ := SourcePreprocessor.program_exec_raw (k^2) (f.map Padding.BinaryEncoding.clauseBits)
  rw [rawInput_eq_formulaBits,MatrixSource.packedSource_eq f hlen] at hp
  have hpbound : tp ≤ 500*(k^2+m+2)^2 := by
    have hs := SourcePreprocessor.sourceCost_bound (k^2) (f.map Padding.BinaryEncoding.clauseBits)
    rw [List.length_map,totalWordLength_clauseBits,hlen] at hs
    have h := htp.trans hs
    nlinarith
  obtain ⟨tg,htg,hg⟩ := hgenerator
  have hside := Sideband.program_exec p gio dims table bits tg hg
  have hgen := ProgramComposition.compose_exec SourcePreprocessor.program (A .input)
    (Sideband.program p gio) (Sideband.I gio) _ _ _ _ _ hp hside
  have hpair : Padding.BinaryEncoding.wordCode bits ++ table = ReductionMachine.pairInput bits table := rfl
  rw [← hpair] at hevaluator
  have hfinal := ProgramComposition.compose_exec (generation p gio) (generationIO p gio)
    ReductionMachine.serializedTableProgram ReductionMachine.Tape.source _ _ _ _ _ hgen hevaluator
  have hb : bits.length = denseLength k m := by simp [bits,ReductionMachine.denseInput,denseLength,MatrixSource.denseLength]
  have hd : dims.length = k+m+2 := by simp [dims,GraphGenerator.dimensions,unary]; omega
  have hpost : (Padding.BinaryEncoding.wordCode bits ++ table).length = 2*bits.length+1+table.length := by
    simp [Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.natCode]
    omega
  have hpre : (Padding.BinaryEncoding.wordCode (GraphGenerator.dimensions k m) ++
      ReductionMachine.denseInput (Padding.matrixCNF f hlen)).length = 2*(k+m+2)+1+denseLength k m := by
    simp [Padding.BinaryEncoding.wordCode,Padding.BinaryEncoding.natCode,GraphGenerator.dimensions,
      ReductionMachine.denseInput,denseLength,MatrixSource.denseLength,unary]
    omega
  refine ⟨_,?_,hfinal⟩
  simp only [hpre,hpost,houtput,hb,hd]
  unfold bound
  nlinarith only [hpbound,htg]

def machine {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (p : Program K L) (gio : K) : FiniteMachine := finiteCompiled (program p gio) (io p gio)

/-- Exact decoded output for the actual bipartite graph. -/
noncomputable def bipOutput {k m : ℕ} (φ : CNF k m) : List Bool :=
  GraphProblem.adjacencyBits (bipGraph φ) (GraphGenerator.bipLabeling k m)

def bipGenerator := extendedGraphProgram bipExtras bipRowProgram

def bipBound (k m : ℕ) : ℕ :=
  bound k m (Fintype.card (Vertex k m)+3) (bipTable k m)
    (extendedGenerationBound bipExtras (bipRowWord (k:=k) (m:=m)) (selectedRowBudget k m))

lemma bipOutput_length {k m : ℕ} (φ : CNF k m) :
    (bipOutput φ).length=(Fintype.card (Vertex k m)+3)^2 := by
  simp [bipOutput,GraphProblem.adjacencyBits_length,bipLabeling,extendedVertices,bipExtras,
    RawPaperOrder.constructionOrderRaw_length]

/-- The already fixed serialized evaluator applied to the exact generated bipartite table. -/
theorem bipEvaluator_exec {k m : ℕ} (φ : CNF k m) :
    Exec ReductionMachine.serializedTableProgram
      ⟨some ReductionMachine.serializedTableProgram.entry,
        ioStacks ReductionMachine.Tape.source (ReductionMachine.pairInput (ReductionMachine.denseInput φ) (bipTable k m))⟩
      ((Fintype.card (Vertex k m)+3)^2*(5*denseLength k m+6)+8*denseLength k m+4*(bipTable k m).length+10)
      ⟨none,ioStacks ReductionMachine.Tape.source (bipOutput φ)⟩ := by
  have h := ReductionMachine.serialized_table_exec
    (FamilyTableEvaluation.bipRows (GraphGenerator.bipLabeling k m).vertices) (ReductionMachine.denseInput φ)
    (FamilyTableEvaluation.bip_masks_length _ φ)
  rw [← bipTable_eq_rows,FamilyTableEvaluation.bip_tableValues,GraphGenerator.bipRows_length] at h
  simpa only [ReductionMachine.denseInput,List.length_map,ReductionMachine.slotList_length,
    denseLength,MatrixSource.denseLength,bipOutput] using h

/-- Actual source-to-bipartite-adjacency trace, with no unproved generation premise. -/
theorem bip_program_exec {k m : ℕ} (hk : 0<k) (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1) :
    ∃ time ≤ bipBound k m,
      Exec (program bipGenerator (G .input))
        ⟨some (program bipGenerator (G .input)).entry,
          ioStacks (io bipGenerator (G .input)) (Padding.BinaryEncoding.formulaBits f)⟩ time
        ⟨none,ioStacks (io bipGenerator (G .input)) (bipOutput (Padding.matrixCNF f hlen))⟩ :=
  program_exec bipGenerator (G .input) f hlen _ _ _ _ (bipOutput_length _)
    (extendedGraphProgram_correct _ _ _ _ (bip_row_correct hk)) (bipEvaluator_exec _)

def bipMachine : FiniteMachine := machine bipGenerator (G .input)

theorem bipMachine_correct {k m : ℕ} (hk : 0<k) (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1) :
    bipMachine.outputsInTime (Padding.BinaryEncoding.formulaBits f)
      (bipOutput (Padding.matrixCNF f hlen)) (bipBound k m) := by
  obtain ⟨time,ht,he⟩ := bip_program_exec hk f hlen
  have cert := outputCertificate (program bipGenerator (G .input)) (io bipGenerator (G .input))
    _ _ time (bipBound k m) he ht
  change Nonempty (Turing.TM2OutputsInTime (compile (program bipGenerator (G .input)) (io bipGenerator (G .input)))
    ((Padding.BinaryEncoding.formulaBits f).map id) (some ((bipOutput (Padding.matrixCNF f hlen)).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

/-- The same fixed-dimensional source pipeline for either reservoir construction. -/
noncomputable def sigmaOutput {k m b : ℕ} (φ : CNF k m) (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) : List Bool :=
  GraphProblem.adjacencyBits (SigmaConstruction.graph φ clique P Q R) (sigmaLabeling k m b)

def sigmaGenerator {b : ℕ} (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :=
  extendedGraphProgram (SigmaWidth.reservoirOrder b) (sigmaRowProgram clique P Q R)

def sigmaBound (k m b : ℕ) (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :=
  bound k m (Fintype.card (Vertex k m)+3*b) (sigmaTable k m b clique P Q R)
    (extendedGenerationBound (SigmaWidth.reservoirOrder b) (sigmaRowWord (k:=k) (m:=m) clique P Q R)
      (selectedRowBudget k m))

lemma sigmaOutput_length {k m b : ℕ} (φ : CNF k m) (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) :
    (sigmaOutput φ clique P Q R).length=(Fintype.card (Vertex k m)+3*b)^2 := by
  simp [sigmaOutput,GraphProblem.adjacencyBits_length,sigmaLabeling,extendedLabeling,extendedVertices,
    SigmaWidth.reservoirOrder,RawPaperOrder.constructionOrderRaw_length]
  ring

theorem sigmaEvaluator_exec {k m b : ℕ} (φ : CNF k m) (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) :
    Exec ReductionMachine.serializedTableProgram
      ⟨some ReductionMachine.serializedTableProgram.entry,
        ioStacks ReductionMachine.Tape.source
          (ReductionMachine.pairInput (ReductionMachine.denseInput φ) (sigmaTable k m b clique P Q R))⟩
      ((Fintype.card (Vertex k m)+3*b)^2*(5*denseLength k m+6)+8*denseLength k m+
        4*(sigmaTable k m b clique P Q R).length+10)
      ⟨none,ioStacks ReductionMachine.Tape.source (sigmaOutput φ clique P Q R)⟩ := by
  have h := ReductionMachine.serialized_table_exec
    (FamilyTableEvaluation.sigmaRows clique P Q R (sigmaLabeling k m b).vertices) (ReductionMachine.denseInput φ)
    (FamilyTableEvaluation.sigma_masks_length clique P Q R _ φ)
  rw [← sigmaTable_eq_rows,FamilyTableEvaluation.sigma_tableValues,GraphGenerator.sigmaRows_length] at h
  simpa only [ReductionMachine.denseInput,List.length_map,ReductionMachine.slotList_length,
    denseLength,MatrixSource.denseLength,sigmaOutput] using h

theorem sigma_program_exec {k m b : ℕ} (hk : 0<k) (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    ∃ time ≤ sigmaBound k m b clique P Q R,
      Exec (program (sigmaGenerator clique P Q R) (G .input))
        ⟨some (program (sigmaGenerator clique P Q R) (G .input)).entry,
          ioStacks (io (sigmaGenerator clique P Q R) (G .input)) (Padding.BinaryEncoding.formulaBits f)⟩ time
        ⟨none,ioStacks (io (sigmaGenerator clique P Q R) (G .input))
          (sigmaOutput (Padding.matrixCNF f hlen) clique P Q R)⟩ :=
  program_exec (sigmaGenerator clique P Q R) (G .input) f hlen _ _ _ _ (sigmaOutput_length _ _ _ _ _)
    (extendedGraphProgram_correct _ _ _ _ (sigma_row_correct hk clique P Q R)) (sigmaEvaluator_exec _ _ _ _ _)

def sigmaMachine {b : ℕ} (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) : FiniteMachine :=
  machine (sigmaGenerator clique P Q R) (G .input)

theorem sigmaMachine_correct {k m b : ℕ} (hk : 0<k) (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) :
    (sigmaMachine clique P Q R).outputsInTime (Padding.BinaryEncoding.formulaBits f)
      (sigmaOutput (Padding.matrixCNF f hlen) clique P Q R) (sigmaBound k m b clique P Q R) := by
  obtain ⟨time,ht,he⟩ := sigma_program_exec hk f hlen clique P Q R
  have cert := outputCertificate (program (sigmaGenerator clique P Q R) (G .input))
    (io (sigmaGenerator clique P Q R) (G .input)) _ _ time (sigmaBound k m b clique P Q R) he ht
  change Nonempty (Turing.TM2OutputsInTime
    (compile (program (sigmaGenerator clique P Q R) (G .input)) (io (sigmaGenerator clique P Q R) (G .input)))
    ((Padding.BinaryEncoding.formulaBits f).map id)
    (some ((sigmaOutput (Padding.matrixCNF f hlen) clique P Q R).map id)) _)
  simpa only [List.map_id] using (show Nonempty _ from ⟨cert⟩)

end ExtendedMatrixSource
end RankwidthDomination
