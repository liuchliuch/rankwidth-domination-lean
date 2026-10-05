# Critical semantic definitions

This compact index identifies the definitions reviewed against the original paper. It is not an alternative source of declarations. The complete authoritative terms remain in `definitions.export.jsonl`; the original Lean source is already included in the repository. Readable rendered terms below may omit proof fields.

`definition-inventory.json` lists all 1,998 names, declaration kinds and original modules. The 81 original source-file hashes and frozen-export hash are in `trusted-definition-provenance.json`. The full expanded audit inventory was retained outside the distribution to avoid duplicating generated program expressions.

## Complexity.FiniteMachine

Finite code and finite alphabets for every internal stack; no infinite-alphabet advice machine.

Source: [RankwidthDomination/Complexity.lean:625](../../../RankwidthDomination/Complexity.lean#L625)

Type: `Type 1`

## Complexity.FiniteMachine.outputsInTime

Actual finite-machine execution returning the required bit sequence within a bounded step count.

Source: [RankwidthDomination/Complexity.lean:632](../../../RankwidthDomination/Complexity.lean#L632)

Type: `RankwidthDomination.Complexity.FiniteMachine → List Bool → List Bool → ℕ → Prop`

Readable definition:

```lean
fun machine input output time =>
  Nonempty
    (Turing.TM2OutputsInTime machine.tm (List.map (⇑machine.inputAlphabet.symm) input)
      (Option.some (List.map (⇑machine.outputAlphabet.symm) output)) time)
```

## Complexity.HasSubexponentialDecision

Uniform decision machine, polynomial source-size factor, and an exponent sublinear in the variable count.

Source: [RankwidthDomination/Complexity.lean:660](../../../RankwidthDomination/Complexity.lean#L660)

Type: `ℕ → Prop`

Readable definition:

```lean
fun q =>
  ∃ machine C,
    0 < C ∧
      ∃ d e,
        RankwidthDomination.Complexity.Sublinear e ∧
          ∀ (n : ℕ) (f : RankwidthDomination.Padding.FlatCNF n),
            RankwidthDomination.Padding.WidthAtMost q f →
              ∃ time,
                machine.outputsInTime (RankwidthDomination.Padding.BinaryEncoding.formulaBits f)
                    (RankwidthDomination.Complexity.satOutput f) time ∧
                  ↑time ≤ C * 2 ^ e n * ↑(n + List.length f + 1) ^ d
```

## Complexity.HasSubexponentialCounting

The matching uniform counting hypothesis over actual encoded formulas and outputs.

Source: [RankwidthDomination/Complexity.lean:668](../../../RankwidthDomination/Complexity.lean#L668)

Type: `ℕ → Prop`

Readable definition:

```lean
fun q =>
  ∃ machine C,
    0 < C ∧
      ∃ d e,
        RankwidthDomination.Complexity.Sublinear e ∧
          ∀ (n : ℕ) (f : RankwidthDomination.Padding.FlatCNF n),
            RankwidthDomination.Padding.WidthAtMost q f →
              ∃ time,
                machine.outputsInTime (RankwidthDomination.Padding.BinaryEncoding.formulaBits f)
                    (RankwidthDomination.Complexity.countOutput f) time ∧
                  ↑time ≤ C * 2 ^ e n * ↑(n + List.length f + 1) ^ d
```

## Complexity.ETH

Negation of a subexponential decision algorithm for clauses of width at most three.

Source: [RankwidthDomination/Complexity.lean:676](../../../RankwidthDomination/Complexity.lean#L676)

Type: `Prop`

Readable definition:

```lean
¬RankwidthDomination.Complexity.HasSubexponentialDecision 3
```

## Complexity.CountingETH

Negation of the corresponding subexponential counting algorithm.

Source: [RankwidthDomination/Complexity.lean:679](../../../RankwidthDomination/Complexity.lean#L679)

Type: `Prop`

Readable definition:

```lean
¬RankwidthDomination.Complexity.HasSubexponentialCounting 3
```

## Complexity.OrdinaryCountingSETH

Ordinary, potentially repeated-clause input; the saving is quantified before a hard clause width is chosen.

Source: [RankwidthDomination/OrdinaryCountingSETH.lean:24](../../../RankwidthDomination/OrdinaryCountingSETH.lean#L24)

Type: `Prop`

Readable definition:

```lean
∀ (δ : ℝ), 0 < δ → δ < 1 → ∃ q, 1 ≤ q ∧ ¬RankwidthDomination.Complexity.HasOrdinaryFixedRateCounting q (1 - δ)
```

## GraphProblem.Solution

Ordinary closed-neighborhood domination, independent or induced-connected variants, open-neighborhood total domination, or actual sigma/rho neighbor counts.

Source: [RankwidthDomination/GraphProblem.lean:30](../../../RankwidthDomination/GraphProblem.lean#L30)

Type: `{V : Type} → [DecidableEq V] → RankwidthDomination.GraphProblem.Problem → SimpleGraph V → Finset V → Prop`

Readable definition:

```lean
fun {V} [DecidableEq V] p G D =>
  match p with
  | RankwidthDomination.GraphProblem.Problem.domination => RankwidthDomination.Dominates G D
  | RankwidthDomination.GraphProblem.Problem.independent =>
    RankwidthDomination.Dominates G D ∧ G.IsIndepSet ↑D
  | RankwidthDomination.GraphProblem.Problem.connected =>
    RankwidthDomination.Dominates G D ∧ RankwidthDomination.ConnectedSelected G D
  | RankwidthDomination.GraphProblem.Problem.total => RankwidthDomination.TotalDominates G D
  | RankwidthDomination.GraphProblem.Problem.sigmaRho σ ρ => RankwidthDomination.IsSigmaRho G σ ρ D
```

## GraphProblem.InClass

The exact unrestricted, monopolar, split, and connected bipartite diameter-at-most-four predicates.

Source: [RankwidthDomination/GraphProblem.lean:57](../../../RankwidthDomination/GraphProblem.lean#L57)

Type: `{V : Type} → RankwidthDomination.GraphProblem.GraphClass → SimpleGraph V → Prop`

Readable definition:

```lean
fun {V} cl G =>
  match cl with
  | RankwidthDomination.GraphProblem.GraphClass.all => True
  | RankwidthDomination.GraphProblem.GraphClass.monopolar => RankwidthDomination.GraphProblem.IsMonopolar G
  | RankwidthDomination.GraphProblem.GraphClass.split => RankwidthDomination.GraphProblem.IsSplit G
  | RankwidthDomination.GraphProblem.GraphClass.bipartiteDiameterFour =>
    RankwidthDomination.GraphProblem.IsBipartiteDiameterFour G
```

## GraphProblem.Certificate

Separate intrinsic-width, supplied-order, and supplied-decomposition input modes.

Source: [RankwidthDomination/GraphProblem.lean:69](../../../RankwidthDomination/GraphProblem.lean#L69)

Type: `RankwidthDomination.GraphProblem.Parameter → Type → Type`

Readable definition:

```lean
fun param V =>
  match param with
  | RankwidthDomination.GraphProblem.Parameter.rankWidth => Unit
  | RankwidthDomination.GraphProblem.Parameter.linearRankWidth => Unit
  | RankwidthDomination.GraphProblem.Parameter.suppliedOrder =>
    RankwidthDomination.WidthParameters.VertexOrder V
  | RankwidthDomination.GraphProblem.Parameter.suppliedDecomposition =>
    RankwidthDomination.RankDecomposition V
```

## GraphProblem.inputBits

The actual vertex count, adjacency bits, target budget and encoded certificate.

Source: [RankwidthDomination/GraphProblem.lean:112](../../../RankwidthDomination/GraphProblem.lean#L112)

Type: `{V : Type} →   [DecidableEq V] →     SimpleGraph V →       RankwidthDomination.WidthParameters.VertexOrder V →         ℕ →           (param : RankwidthDomination.GraphProblem.Parameter) →             RankwidthDomination.GraphProblem.Certificate param V → List Bool`

Readable definition:

```lean
fun {V} [DecidableEq V] G labeling d param cert =>
  RankwidthDomination.Padding.BinaryEncoding.natCode labeling.vertices.length ++
        RankwidthDomination.Padding.BinaryEncoding.natCode d ++
      RankwidthDomination.GraphProblem.adjacencyBits G labeling ++
    RankwidthDomination.GraphProblem.certificateBits labeling param cert
```

## GraphProblem.outputBits

Decision, at-most-target count, or exact-target count over actual finite solution sets.

Source: [RankwidthDomination/GraphProblem.lean:129](../../../RankwidthDomination/GraphProblem.lean#L129)

Type: `{V : Type} →   [Fintype V] →     [DecidableEq V] →       RankwidthDomination.GraphProblem.Problem →         SimpleGraph V → ℕ → RankwidthDomination.GraphProblem.Goal → List Bool`

Readable definition:

```lean
fun {V} [Fintype V] [DecidableEq V] p G d goal =>
  match goal with
  | RankwidthDomination.GraphProblem.Goal.decision =>
    [Decidable.decide (∃ D, RankwidthDomination.GraphProblem.Solution p G D ∧ D.card ≤ d)]
  | RankwidthDomination.GraphProblem.Goal.countAtMost =>
    Computability.encodeNat (RankwidthDomination.GraphProblem.countAtMost p G d)
  | RankwidthDomination.GraphProblem.Goal.countExactly =>
    Computability.encodeNat (RankwidthDomination.GraphProblem.countExactly p G d)
```

## GraphProblem.parameterValue

The parameter is computed from the graph or supplied object, rather than an unchecked claimed bound.

Source: [RankwidthDomination/GraphProblem.lean:75](../../../RankwidthDomination/GraphProblem.lean#L75)

Type: `{V : Type} →   [Fintype V] →     SimpleGraph V →       (param : RankwidthDomination.GraphProblem.Parameter) →         RankwidthDomination.GraphProblem.Certificate param V → ℕ`

Readable definition:

```lean
fun {V} [Fintype V] G param =>
  match (motive :=
    (param : RankwidthDomination.GraphProblem.Parameter) →
      RankwidthDomination.GraphProblem.Certificate param V → ℕ)
    param with
  | RankwidthDomination.GraphProblem.Parameter.rankWidth => fun x =>
    RankwidthDomination.WidthParameters.rankWidth G
  | RankwidthDomination.GraphProblem.Parameter.linearRankWidth => fun x =>
    RankwidthDomination.WidthParameters.linearRankWidth G
  | RankwidthDomination.GraphProblem.Parameter.suppliedOrder => fun o =>
    RankwidthDomination.WidthParameters.VertexOrder.width G o
  | RankwidthDomination.GraphProblem.Parameter.suppliedDecomposition => fun d =>
    RankwidthDomination.RankDecomposition.width d G
```

## GraphProblem.HasSubquadraticAlgorithm

A uniform finite solver with the intended 2^o(w²) polynomial-vertex-count bound.

Source: [RankwidthDomination/GraphProblem.lean:140](../../../RankwidthDomination/GraphProblem.lean#L140)

Type: `RankwidthDomination.GraphProblem.Problem →   RankwidthDomination.GraphProblem.GraphClass →     RankwidthDomination.GraphProblem.Parameter → RankwidthDomination.GraphProblem.Goal → Prop`

Readable definition:

```lean
fun p cl param goal =>
  ∃ machine C,
    0 < C ∧
      ∃ d exponent,
        RankwidthDomination.Complexity.Subquadratic exponent ∧
          ∀ (V : Type) (x : Fintype V) (x_1 : DecidableEq V) (G : SimpleGraph V)
            (labeling : RankwidthDomination.WidthParameters.VertexOrder V),
            ∀ target ≤ Fintype.card V,
              RankwidthDomination.GraphProblem.InClass cl G →
                ∀ (cert : RankwidthDomination.GraphProblem.Certificate param V),
                  ∃ time,
                    machine.outputsInTime
                        (RankwidthDomination.GraphProblem.inputBits G labeling target param cert)
                        (RankwidthDomination.GraphProblem.outputBits p G target goal) time ∧
                      ↑time ≤
                        C * 2 ^ exponent (RankwidthDomination.GraphProblem.parameterValue G param cert) *
                          ↑(Fintype.card V + 1) ^ d
```

## GraphProblem.HasQuadraticRateAlgorithm

The same exact input/output semantics with a specified quadratic-exponent coefficient.

Source: [RankwidthDomination/GraphProblem.lean:153](../../../RankwidthDomination/GraphProblem.lean#L153)

Type: `RankwidthDomination.GraphProblem.Problem →   RankwidthDomination.GraphProblem.GraphClass →     RankwidthDomination.GraphProblem.Parameter → RankwidthDomination.GraphProblem.Goal → ℝ → Prop`

Readable definition:

```lean
fun p cl param goal rate =>
  ∃ machine C,
    0 < C ∧
      ∃ d,
        ∀ (V : Type) (x : Fintype V) (x_1 : DecidableEq V) (G : SimpleGraph V)
          (labeling : RankwidthDomination.WidthParameters.VertexOrder V),
          ∀ target ≤ Fintype.card V,
            RankwidthDomination.GraphProblem.InClass cl G →
              ∀ (cert : RankwidthDomination.GraphProblem.Certificate param V),
                ∃ time,
                  machine.outputsInTime
                      (RankwidthDomination.GraphProblem.inputBits G labeling target param cert)
                      (RankwidthDomination.GraphProblem.outputBits p G target goal) time ∧
                    ↑time ≤
                      C * 2 ^ (rate * ↑(RankwidthDomination.GraphProblem.parameterValue G param cert) ^ 2) *
                        ↑(Fintype.card V + 1) ^ d
```

## WidthParameters.rankWidth

Minimum width over genuine finite graph-theoretic rank decompositions.

Source: [RankwidthDomination/WidthParameters.lean:219](../../../RankwidthDomination/WidthParameters.lean#L219)

Type: `{V : Type u_1} → [Fintype V] → SimpleGraph V → ℕ`

Readable definition:

```lean
fun {V} [Fintype V] G => if Fintype.card V < 2 then 0 else InfSet.sInf (Set.range fun d => d.width G)
```

## WitnessedRankWidth.HasRankWidthAlgorithm

Allows a supplied witness while the running-time parameter remains intrinsic graph rank-width.

Source: [RankwidthDomination/WitnessedRankWidth.lean:20](../../../RankwidthDomination/WitnessedRankWidth.lean#L20)

Type: `RankwidthDomination.GraphProblem.Problem →   RankwidthDomination.GraphProblem.GraphClass →     RankwidthDomination.WitnessedRankWidth.WitnessMode → RankwidthDomination.GraphProblem.Goal → Prop`

Readable definition:

```lean
fun problem cl mode goal =>
  ∃ machine C,
    0 < C ∧
      ∃ d e,
        RankwidthDomination.Complexity.Subquadratic e ∧
          ∀ (V : Type) (x : Fintype V) (x_1 : DecidableEq V) (G : SimpleGraph V)
            (labeling : RankwidthDomination.WidthParameters.VertexOrder V),
            ∀ target ≤ Fintype.card V,
              RankwidthDomination.GraphProblem.InClass cl G →
                ∀ (cert : RankwidthDomination.GraphProblem.Certificate mode.parameter V),
                  ∃ time,
                    machine.outputsInTime
                        (RankwidthDomination.GraphProblem.inputBits G labeling target mode.parameter cert)
                        (RankwidthDomination.GraphProblem.outputBits problem G target goal) time ∧
                      ↑time ≤
                        C * 2 ^ e (RankwidthDomination.WidthParameters.rankWidth G) *
                          ↑(Fintype.card V + 1) ^ d
```

## Satisfies

Every actual CNF clause has a satisfied row-indexed literal under the assignment matrix.

Source: [RankwidthDomination/Basic.lean:18](../../../RankwidthDomination/Basic.lean#L18)

Type: `{k m : ℕ} → RankwidthDomination.CNF k m → RankwidthDomination.Assignment k → Prop`

Readable definition:

```lean
fun {k m} φ X => ∀ (h : Fin (m + 1)), ∃ a, RankwidthDomination.RowSatisfies φ h a (X a)
```

## coreAdj

All original choice/guard/clause/checker adjacency cases and the optional split completion.

Source: [RankwidthDomination/Basic.lean:42](../../../RankwidthDomination/Basic.lean#L42)

Type: `{k m : ℕ} →   RankwidthDomination.CNF k m → Bool → RankwidthDomination.Vertex k m → RankwidthDomination.Vertex k m → Prop`

Readable definition:

```lean
fun {k m} φ split x x_1 =>
  match x, x_1 with
  | RankwidthDomination.Vertex.choice h a x, RankwidthDomination.Vertex.choice h' a' x' =>
    (h ≠ h' ∨ a ≠ a' ∨ x ≠ x') ∧ (split = Bool.true ∨ h = h' ∧ a = a')
  | RankwidthDomination.Vertex.guard h a a_1, RankwidthDomination.Vertex.choice h' a' a_2 => h = h' ∧ a = a'
  | RankwidthDomination.Vertex.choice h a a_1, RankwidthDomination.Vertex.guard h' a' a_2 => h = h' ∧ a = a'
  | RankwidthDomination.Vertex.clause h, RankwidthDomination.Vertex.choice h' a x =>
    h = h' ∧ RankwidthDomination.RowSatisfies φ h a x
  | RankwidthDomination.Vertex.choice h a x, RankwidthDomination.Vertex.clause h' =>
    h = h' ∧ RankwidthDomination.RowSatisfies φ h' a x
  | RankwidthDomination.Vertex.checker i c, RankwidthDomination.Vertex.choice h a x =>
    RankwidthDomination.checkerChoiceAdj i c h a x
  | RankwidthDomination.Vertex.choice h a x, RankwidthDomination.Vertex.checker i c =>
    RankwidthDomination.checkerChoiceAdj i c h a x
  | x, x_2 => False
```

## cutRank

Rank over the binary field of the actual adjacency submatrix across a cut.

Source: [RankwidthDomination/Layout.lean:20](../../../RankwidthDomination/Layout.lean#L20)

Type: `{V : Type u_1} → [Fintype V] → SimpleGraph V → Set V → ℕ`

Readable definition:

```lean
fun {V} [Fintype V] G S => (RankwidthDomination.cutMatrix G S).rank
```

## IsSigmaRho

Counts selected open neighbors and applies sigma inside the solution, rho outside.

Source: [RankwidthDomination/SigmaRho.lean:19](../../../RankwidthDomination/SigmaRho.lean#L19)

Type: `{V : Type u_1} →   [DecidableEq V] → (G : SimpleGraph V) → [DecidableRel G.Adj] → Set ℕ → Set ℕ → Finset V → Prop`

Readable definition:

```lean
fun {V} [DecidableEq V] G [DecidableRel G.Adj] σ ρ S =>
  ∀ (v : V),
    if v ∈ S then (RankwidthDomination.selectedNeighbors G S v).card ∈ σ
    else (RankwidthDomination.selectedNeighbors G S v).card ∈ ρ
```

## B1RAM.output

The explicitly charged construction returns the true standard-basis tree together with its full tagged serialization.

Source: [RankwidthDomination/B1RAMSerialization.lean:94](../../../RankwidthDomination/B1RAMSerialization.lean#L94)

Type: `(k m : ℕ) →   RankwidthDomination.B1RAM.Run     (RankwidthDomination.RankTree (RankwidthDomination.Standard.Vertex k m) × List ℕ)`

Readable definition:

```lean
fun k m =>
  let t := RankwidthDomination.B1RAM.standard k m;
  let w := RankwidthDomination.B1RAM.writeTree RankwidthDomination.B1RAM.writeVertex t.1;
  ((t.1, k :: m :: w.1), t.2 + w.2 + 5)
```

## StandardAdjacencyAlgorithm.coreMatrix

Explicit input decoding, vertex generation, adjacency evaluation and matrix output; no graph-generation oracle.

Source: [RankwidthDomination/StandardAdjacencyAlgorithm.lean:630](../../../RankwidthDomination/StandardAdjacencyAlgorithm.lean#L630)

Type: `ℕ → ℕ → Bool → List Bool → RankwidthDomination.B1RAM.Run (List Bool)`

Readable definition:

```lean
fun k m split input =>
  let source := RankwidthDomination.StandardAdjacencyAlgorithm.decodeSource k m input;
  let vs := RankwidthDomination.StandardAdjacencyAlgorithm.vertices k m;
  let result :=
    RankwidthDomination.StandardAdjacencyAlgorithm.matrix
      (RankwidthDomination.StandardAdjacencyAlgorithm.coreEdge source.1.1 split) vs.1;
  (result.1, source.2 + vs.2 + result.2 + 2)
```

## SplitPerfectCode.PerfectCode

Exactly one chosen vertex in every closed neighborhood, including vacuous behavior on an empty graph.

Source: [RankwidthDomination/PerfectCode.lean:21](../../../RankwidthDomination/PerfectCode.lean#L21)

Type: `{V : Type u_1} → SimpleGraph V → Finset V → Prop`

Readable definition:

```lean
fun {V} G D => ∀ (v : V), ∃! d, d ∈ D ∧ (v = d ∨ G.Adj v d)
```

## SplitPerfectCode.solve

The concrete adjacency-list scan returns an implicit complete representation and exact count.

Source: [RankwidthDomination/PerfectCode.lean:549](../../../RankwidthDomination/PerfectCode.lean#L549)

Type: `{V : Type u_1} →   [inst : DecidableEq V] →     {G : SimpleGraph V} →       {C I : Finset V} →         RankwidthDomination.SplitPerfectCode.AdjacencyInput G C I →           RankwidthDomination.SplitPerfectCode.Result V`

Readable definition:

```lean
fun {V} [DecidableEq V] {G} {C I} A =>
  let ci := RankwidthDomination.SplitPerfectCode.scanClique A.inI A.neighbors A.cliqueVertices;
  let ii := RankwidthDomination.SplitPerfectCode.scanIndependent A.neighbors A.independentVertices;
  let out := RankwidthDomination.SplitPerfectCode.scanCenters ii.active ci.1;
  { zero := ii.zero, good := out.good, allOne := out.allOne, independentSize := A.independentVertices.length,
    zeroSize := ii.zero.length, number := (if out.allOne = Bool.true then 1 else 0) + out.good.length,
    cost := ci.2 + ii.cost + out.cost + A.independentVertices.length + ii.zero.length + out.good.length + 3 }
```

## SplitPerfectCode.optimize

Both extrema share one solve result; the separate contracts establish their actual set cardinalities and linear operational cost.

Source: [RankwidthDomination/PerfectCode.lean:974](../../../RankwidthDomination/PerfectCode.lean#L974)

Type: `{V : Type u_1} →   [inst : DecidableEq V] →     {G : SimpleGraph V} →       {C I : Finset V} →         RankwidthDomination.SplitPerfectCode.AdjacencyInput G C I →           RankwidthDomination.SplitPerfectCode.OptimizationResult V`

Readable definition:

```lean
fun {V} [DecidableEq V] {G} {C I} A =>
  let R := RankwidthDomination.SplitPerfectCode.solve A;
  let lo :=
    Option.map (RankwidthDomination.SplitPerfectCode.materializeResult A.independentVertices R)
      (RankwidthDomination.SplitPerfectCode.minimumChoice R);
  let hi :=
    Option.map (RankwidthDomination.SplitPerfectCode.materializeResult A.independentVertices R)
      (RankwidthDomination.SplitPerfectCode.maximumChoice R);
  { representation := R, minimum := lo, maximum := hi,
    cost := R.cost + (Option.map List.length lo).getD 0 + (Option.map List.length hi).getD 0 + 2 }
```
