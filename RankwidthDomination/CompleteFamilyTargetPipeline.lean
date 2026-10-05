import RankwidthDomination.TargetAssembly
import RankwidthDomination.MetadataSource
import RankwidthDomination.TargetMetadataUniform
import RankwidthDomination.ExtendedMatrixSource
import RankwidthDomination.GeneratedLabelWidths

/-! Complete source-to-target encoders for the bipartite and fixed reservoir
families. A single finite program, fixed before seeing the input formula, makes
both the adjacency matrix and the actual complete order or decomposition. -/
namespace RankwidthDomination.CompleteFamilyTargetPipeline
open Complexity TargetMetadataMachine WitnessDimensions WitnessMachine Padding.BinaryEncoding
open WidthParameters
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1000000
set_option maxHeartbeats 3000000

abbrev metadataProgram (v t : ℕ) (p : GraphProblem.Parameter) :=
  MetadataSource.program (familyProgram v t p) Register.input
abbrev metaIO (v t : ℕ) (p : GraphProblem.Parameter) :=
  MetadataSource.inputIO (familyProgram v t p) Register.input

/-- The code depends only on the fixed graph family and parameter mode. -/
def machine {K L : Type} [DecidableEq K] [Fintype K] [Fintype L]
    (matrix : Program K L) (io : K) (v t : ℕ) (p : GraphProblem.Parameter) : FiniteMachine :=
  TargetAssembly.machine matrix io (metadataProgram v t p) (metaIO v t p)

/-- Numerical resource bound for the exact fork, metadata generation and splice. -/
def familyBound (k m v t : ℕ) (p : GraphProblem.Parameter)
    (sourceLen n certLen matrixBound : ℕ) : ℕ :=
  matrixBound + 600*(k^2+m+2)^2 + familyTime v t k m p + 4*(k+m+2) +
    69*sourceLen + 55*n^2 + 46*(header n (targetBudget k m+t)).length + 20*certLen + 138

private theorem dimensions_eq (k m : ℕ) :
    SourcePreprocessor.dimensions k m = dimensionInput k m := by
  simp [SourcePreprocessor.dimensions,dimensionInput,natCode,List.append_assoc]

/-- A real matrix trace is joined to the proved family metadata program. There
is no assumed certificate-construction algorithm in this composition lemma. -/
theorem family_machine_correct {K L V : Type} [DecidableEq K] [Fintype K] [Fintype L]
    [DecidableEq V] (matrix : Program K L) (io : K)
    {k m : ℕ} (f : Padding.FlatCNF (k^2)) (hlen : f.length=m+1)
    (G : SimpleGraph V) (labeling : VertexOrder V) (hne : labeling.vertices ≠ [])
    (v t : ℕ) (p : GraphProblem.Parameter) (hsize : labeling.vertices.length=vertexCount k m+v)
    (matrixBound : ℕ)
    (hmatrix : ∃ tm ≤ matrixBound,
      Exec matrix ⟨some matrix.entry,ioStacks io (formulaBits f)⟩ tm
        ⟨none,ioStacks io (GraphProblem.adjacencyBits G labeling)⟩) :
    (machine matrix io v t p).outputsInTime (formulaBits f)
      (GraphProblem.inputBits G labeling (targetBudget k m+t) p (familyCertificate labeling hne p))
      (familyBound k m v t p (formulaBits f).length labeling.vertices.length
        (GraphProblem.certificateBits labeling p (familyCertificate labeling hne p)).length matrixBound) := by
  let c := GraphProblem.certificateBits labeling p (familyCertificate labeling hne p)
  let h := header labeling.vertices.length (targetBudget k m+t)
  obtain ⟨tm,htm,hm⟩ := hmatrix
  have hh := familyProgram_exec labeling hne v t k m p hsize
  rw [← dimensions_eq k m] at hh
  obtain ⟨th,hth,hh⟩ := MetadataSource.program_exec (familyProgram v t p) Register.input f hlen _ _ hh
  have ho := TargetAssembly.machine_outputs matrix io (metadataProgram v t p) (metaIO v t p)
    (formulaBits f) (GraphProblem.adjacencyBits G labeling) h c tm th hm hh
  have hout : h ++ GraphProblem.adjacencyBits G labeling ++ c =
      GraphProblem.inputBits G labeling (targetBudget k m+t) p (familyCertificate labeling hne p) := by
    simp only [h,c,header,GraphProblem.inputBits,List.append_assoc]
  rw [hout] at ho
  apply FiniteMachine.outputsInTime_mono _ ho
  rw [GraphProblem.adjacencyBits_length]
  have hlenmeta : (metadata labeling.vertices.length (targetBudget k m+t) c).length =
      2*h.length+1+c.length := by
    simp [metadata,framedHeader,wordCode,natCode,h]
    omega
  change th ≤ 600*(k^2+m+2)^2+familyTime v t k m p+4*(k+m+2)+
    4*(metadata labeling.vertices.length (targetBudget k m+t) c).length+8 at hth
  rw [hlenmeta] at hth
  change _ ≤ matrixBound + 600*(k^2+m+2)^2 + familyTime v t k m p + 4*(k+m+2) +
    69*(formulaBits f).length + 55*labeling.vertices.length^2 + 46*h.length + 20*c.length + 138
  omega

lemma bipLabeling_length (k m : ℕ) :
    (GraphGenerator.bipLabeling k m).vertices.length=vertexCount k m+3 := by
  rw [GraphProblem.labeling_length,GraphSize.bip_card,vertexCount_eq_card]

lemma sigmaLabeling_length (k m b : ℕ) :
    (GraphGenerator.sigmaLabeling k m b).vertices.length=vertexCount k m+3*b := by
  rw [GraphProblem.labeling_length,GraphSize.sigma_card,vertexCount_eq_card]

lemma bipLabeling_ne_nil (k m : ℕ) : (GraphGenerator.bipLabeling k m).vertices ≠ [] := by
  intro h
  have hc := (GraphGenerator.bipLabeling k m).complete BipVertex.hub
  simpa [h] using hc

lemma sigmaLabeling_ne_nil (k m b : ℕ) : (GraphGenerator.sigmaLabeling k m b).vertices ≠ [] := by
  intro h
  have hc := (GraphGenerator.sigmaLabeling k m b).complete (Sum.inl (Vertex.clause 0))
  simpa [h] using hc

def bipCertificate (k m : ℕ) (p : GraphProblem.Parameter) : GraphProblem.Certificate p (BipVertex k m) :=
  familyCertificate (GraphGenerator.bipLabeling k m) (bipLabeling_ne_nil k m) p

def sigmaCertificate (k m b : ℕ) (p : GraphProblem.Parameter) :
    GraphProblem.Certificate p (SigmaConstruction.V k m b) :=
  familyCertificate (GraphGenerator.sigmaLabeling k m b) (sigmaLabeling_ne_nil k m b) p

/-- Actual bipartite target, including its serialized certificate. -/
noncomputable def bipTarget {k m : ℕ} (φ : CNF k m) (p : GraphProblem.Parameter) : List Bool :=
  GraphProblem.inputBits (bipGraph φ) (GraphGenerator.bipLabeling k m)
    ((m+1)*k+1) p (bipCertificate k m p)

def bipMachine (p : GraphProblem.Parameter) : FiniteMachine :=
  machine (ExtendedMatrixSource.program ExtendedMatrixSource.bipGenerator (GraphGenerator.G .input))
    (ExtendedMatrixSource.io ExtendedMatrixSource.bipGenerator (GraphGenerator.G .input)) 3 1 p

def bipBound {k m : ℕ} (f : Padding.FlatCNF (k^2)) (_hlen : f.length=m+1)
    (p : GraphProblem.Parameter) : ℕ :=
  familyBound k m 3 1 p (formulaBits f).length (vertexCount k m+3)
    (GraphProblem.certificateBits (GraphGenerator.bipLabeling k m) p (bipCertificate k m p)).length
    (ExtendedMatrixSource.bipBound k m)

/-- One fixed finite machine produces the full bipartite problem instance from
source formula bits, without any assumed metadata or table premise. -/
theorem bipMachine_correct {k m : ℕ} (hk : 0<k) (f : Padding.FlatCNF (k^2))
    (hlen : f.length=m+1) (p : GraphProblem.Parameter) :
    (bipMachine p).outputsInTime (formulaBits f)
      (bipTarget (Padding.matrixCNF f hlen) p) (bipBound f hlen p) := by
  have h := family_machine_correct
    (ExtendedMatrixSource.program ExtendedMatrixSource.bipGenerator (GraphGenerator.G .input))
    (ExtendedMatrixSource.io ExtendedMatrixSource.bipGenerator (GraphGenerator.G .input)) f hlen
    (bipGraph (Padding.matrixCNF f hlen)) (GraphGenerator.bipLabeling k m) (bipLabeling_ne_nil k m)
    3 1 p (bipLabeling_length k m) (ExtendedMatrixSource.bipBound k m)
    (ExtendedMatrixSource.bip_program_exec hk f hlen)
  simpa only [bipMachine,bipTarget,bipBound,bipCertificate,targetBudget,bipLabeling_length] using h

/-- Both reservoir branches use the actual same fixed-prefix labeling. -/
noncomputable def sigmaTarget {k m b : ℕ} (φ : CNF k m) (clique : Bool)
    (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (p : GraphProblem.Parameter) : List Bool :=
  GraphProblem.inputBits (SigmaConstruction.graph φ clique P Q R) (GraphGenerator.sigmaLabeling k m b)
    ((m+1)*k+b) p (sigmaCertificate k m b p)

def sigmaMachine {b : ℕ} (clique : Bool) (P Q : Finset (Fin b))
    (R : Fin b → Finset (Fin b)) (p : GraphProblem.Parameter) : FiniteMachine :=
  machine (ExtendedMatrixSource.program (ExtendedMatrixSource.sigmaGenerator clique P Q R) (GraphGenerator.G .input))
    (ExtendedMatrixSource.io (ExtendedMatrixSource.sigmaGenerator clique P Q R) (GraphGenerator.G .input)) (3*b) b p

def sigmaBound {k m b : ℕ} (f : Padding.FlatCNF (k^2)) (_hlen : f.length=m+1)
    (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b)) (p : GraphProblem.Parameter) : ℕ :=
  familyBound k m (3*b) b p (formulaBits f).length (vertexCount k m+3*b)
    (GraphProblem.certificateBits (GraphGenerator.sigmaLabeling k m b) p (sigmaCertificate k m b p)).length
    (ExtendedMatrixSource.sigmaBound k m b clique P Q R)

/-- Every fixed reservoir graph problem has its own fixed finite source encoder.
Only its input data, and never its finite control, depends on k and m. -/
theorem sigmaMachine_correct {k m b : ℕ} (hk : 0<k) (f : Padding.FlatCNF (k^2))
    (hlen : f.length=m+1) (clique : Bool) (P Q : Finset (Fin b)) (R : Fin b → Finset (Fin b))
    (p : GraphProblem.Parameter) :
    (sigmaMachine clique P Q R p).outputsInTime (formulaBits f)
      (sigmaTarget (Padding.matrixCNF f hlen) clique P Q R p) (sigmaBound f hlen clique P Q R p) := by
  have h := family_machine_correct
    (ExtendedMatrixSource.program (ExtendedMatrixSource.sigmaGenerator clique P Q R) (GraphGenerator.G .input))
    (ExtendedMatrixSource.io (ExtendedMatrixSource.sigmaGenerator clique P Q R) (GraphGenerator.G .input)) f hlen
    (SigmaConstruction.graph (Padding.matrixCNF f hlen) clique P Q R) (GraphGenerator.sigmaLabeling k m b)
    (sigmaLabeling_ne_nil k m b) (3*b) b p (sigmaLabeling_length k m b)
    (ExtendedMatrixSource.sigmaBound k m b clique P Q R)
    (ExtendedMatrixSource.sigma_program_exec hk f hlen clique P Q R)
  simpa only [sigmaMachine,sigmaTarget,sigmaBound,sigmaCertificate,targetBudget,sigmaLabeling_length] using h

end RankwidthDomination.CompleteFamilyTargetPipeline
