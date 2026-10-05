/- Mechanically extracted regression layer. Independently written paper
contracts are in ManualMain.lean and ManualGraph.lean. -/
import RankwidthDomination
import ManualMain
import ManualGraph
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Paper 1.1; component RankwidthDomination.MainResults.theorem_1_1_decision. -/
theorem RankwidthPaper.result_1_1_1 :
    RankwidthDomination.Complexity.ETH →
  ∀ {problem : RankwidthDomination.GraphProblem.Problem} {cl : RankwidthDomination.GraphProblem.GraphClass},
    RankwidthDomination.MainResults.PaperCase problem cl →
      ∀ (p : RankwidthDomination.GraphProblem.Parameter),
        Not
          (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm problem cl p
            RankwidthDomination.GraphProblem.Goal.decision) := by
  exact @RankwidthDomination.MainResults.theorem_1_1_decision

/-- Paper 1.1; component RankwidthDomination.MainResults.theorem_1_1_counting. -/
theorem RankwidthPaper.result_1_1_2 :
    RankwidthDomination.Complexity.CountingETH →
  ∀ {problem : RankwidthDomination.GraphProblem.Problem} {cl : RankwidthDomination.GraphProblem.GraphClass},
    RankwidthDomination.MainResults.PaperCase problem cl →
      ∀ (p : RankwidthDomination.GraphProblem.Parameter) (goal : RankwidthDomination.GraphProblem.Goal),
        @Ne.{1} RankwidthDomination.GraphProblem.Goal goal RankwidthDomination.GraphProblem.Goal.decision →
          Not (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm problem cl p goal) := by
  exact @RankwidthDomination.MainResults.theorem_1_1_counting

/-- Paper 2.1; component RankwidthDomination.LowerBounds.square_ETH. -/
theorem RankwidthPaper.result_2_1_1 :
    RankwidthDomination.Complexity.ETH →
  Not
    (RankwidthDomination.LowerBounds.HasSquareSubexponential
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      RankwidthDomination.LowerBounds.SourceGoal.decision) := by
  exact @RankwidthDomination.LowerBounds.square_ETH

/-- Paper 2.1; component RankwidthDomination.LowerBounds.square_countingETH. -/
theorem RankwidthPaper.result_2_1_2 :
    RankwidthDomination.Complexity.CountingETH →
  Not
    (RankwidthDomination.LowerBounds.HasSquareSubexponential
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      RankwidthDomination.LowerBounds.SourceGoal.counting) := by
  exact @RankwidthDomination.LowerBounds.square_countingETH

/-- Paper 2.1; component RankwidthDomination.Padding.squarePad_count. -/
theorem RankwidthPaper.result_2_1_3 :
    ∀ {n : Nat} (f : RankwidthDomination.Padding.FlatCNF n),
  @Eq.{1} Nat
    (@RankwidthDomination.Padding.count
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (RankwidthDomination.Padding.squareSide n)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@RankwidthDomination.Padding.squarePad n f))
    (@RankwidthDomination.Padding.count n f) := by
  exact @RankwidthDomination.Padding.squarePad_count

/-- Paper 2.1; component RankwidthDomination.PaddingPipeline.machine_squarePad. -/
theorem RankwidthPaper.result_2_1_4 :
    ∀ {n : Nat} (f : RankwidthDomination.Padding.FlatCNF n),
  @Exists.{1} Nat fun time =>
    And
      (@LE.le.{0} Nat instLENat time
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2000) (instOfNatNat (nat_lit 2000)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@List.length.{0} (RankwidthDomination.Padding.FlatClause n) f))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
      (RankwidthDomination.PaddingPipeline.machine.outputsInTime
        (@RankwidthDomination.Padding.BinaryEncoding.formulaBits n f)
        (@RankwidthDomination.Padding.BinaryEncoding.formulaBits
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (RankwidthDomination.Padding.squareSide n)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@RankwidthDomination.Padding.squarePad n f))
        time) := by
  exact @RankwidthDomination.PaddingPipeline.machine_squarePad

/-- Paper 3.1; component RankwidthDomination.MainResults.theorem_3_1. -/
theorem RankwidthPaper.result_3_1_1 :
    RankwidthDomination.Complexity.ETH →
  ∀ (cl : RankwidthDomination.GraphProblem.GraphClass),
    RankwidthDomination.MainResults.DominationClass cl →
      ∀ (p : RankwidthDomination.GraphProblem.Parameter),
        Not
          (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
            RankwidthDomination.GraphProblem.Problem.domination cl p
            RankwidthDomination.GraphProblem.Goal.decision) := by
  exact @RankwidthDomination.MainResults.theorem_3_1

/-- Paper 3.1; component RankwidthDomination.CompleteTargetPipeline.machine_correct. -/
theorem RankwidthPaper.result_3_1_2 :
    ∀ {k m : Nat} (hk : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k)
  (f :
    RankwidthDomination.Padding.FlatCNF
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (hlen :
    @Eq.{1} Nat
      (@List.length.{0}
        (RankwidthDomination.Padding.FlatClause
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        f)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (split : Bool) (p : RankwidthDomination.GraphProblem.Parameter),
  (RankwidthDomination.CompleteTargetPipeline.machine split p).outputsInTime
    (@RankwidthDomination.Padding.BinaryEncoding.formulaBits
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      f)
    (@RankwidthDomination.CompleteTargetPipeline.target k m
      (@RankwidthDomination.Padding.matrixCNF k m f hlen) hk split p)
    (@RankwidthDomination.CompleteTargetPipeline.bound k m f hlen hk split p) := by
  exact @RankwidthDomination.CompleteTargetPipeline.machine_correct

/-- Paper 3.1; component RankwidthDomination.CompleteFamilyTargetPipeline.bipMachine_correct. -/
theorem RankwidthPaper.result_3_1_3 :
    ∀ {k m : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    ∀
      (f :
        RankwidthDomination.Padding.FlatCNF
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (hlen :
        @Eq.{1} Nat
          (@List.length.{0}
            (RankwidthDomination.Padding.FlatClause
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            f)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (p : RankwidthDomination.GraphProblem.Parameter),
      (RankwidthDomination.CompleteFamilyTargetPipeline.bipMachine p).outputsInTime
        (@RankwidthDomination.Padding.BinaryEncoding.formulaBits
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          f)
        (@RankwidthDomination.CompleteFamilyTargetPipeline.bipTarget k m
          (@RankwidthDomination.Padding.matrixCNF k m f hlen) p)
        (@RankwidthDomination.CompleteFamilyTargetPipeline.bipBound k m f hlen p) := by
  exact @RankwidthDomination.CompleteFamilyTargetPipeline.bipMachine_correct

/-- Paper 3.2; component RankwidthDomination.MainResults.theorem_3_2. -/
theorem RankwidthPaper.result_3_2_1 :
    RankwidthDomination.Complexity.CountingETH →
  ∀ (cl : RankwidthDomination.GraphProblem.GraphClass),
    RankwidthDomination.MainResults.DominationClass cl →
      ∀ (p : RankwidthDomination.GraphProblem.Parameter) (goal : RankwidthDomination.GraphProblem.Goal),
        @Ne.{1} RankwidthDomination.GraphProblem.Goal goal RankwidthDomination.GraphProblem.Goal.decision →
          Not
            (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
              RankwidthDomination.GraphProblem.Problem.domination cl p goal) := by
  exact @RankwidthDomination.MainResults.theorem_3_2

/-- Paper 3.3; component RankwidthDomination.domination_card_lower_bound. -/
theorem RankwidthPaper.result_3_3_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (s : Bool) (D : Finset.{0} (RankwidthDomination.Vertex k m)),
  @RankwidthDomination.Dominates.{0} (RankwidthDomination.Vertex k m)
      (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ s) D →
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        k)
      (@Finset.card.{0} (RankwidthDomination.Vertex k m) D) := by
  exact @RankwidthDomination.domination_card_lower_bound

/-- Paper 3.3; component RankwidthDomination.tight_normal_form. -/
theorem RankwidthPaper.result_3_3_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (s : Bool) (D : Finset.{0} (RankwidthDomination.Vertex k m)),
  @RankwidthDomination.Dominates.{0} (RankwidthDomination.Vertex k m)
      (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ s) D →
    @LE.le.{0} Nat instLENat (@Finset.card.{0} (RankwidthDomination.Vertex k m) D)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          k) →
      @Exists.{1}
        (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          RankwidthDomination.Assignment k)
        fun R =>
        And (@Eq.{1} (Finset.{0} (RankwidthDomination.Vertex k m)) D (@RankwidthDomination.selected k m R))
          (@Eq.{1} Nat (@Finset.card.{0} (RankwidthDomination.Vertex k m) D)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)) := by
  exact @RankwidthDomination.tight_normal_form

/-- Paper 3.4; component RankwidthDomination.checker_no_neighbor_iff. -/
theorem RankwidthPaper.result_3_4_1 :
    ∀ {k : Nat} (X Y : RankwidthDomination.Assignment k) (t p r : RankwidthDomination.Row k),
  Iff (Not (@RankwidthDomination.checkerHasNeighbor k X Y t p r))
    (And
      (@Eq.{1} (Fin k → RankwidthDomination.Bit)
        (@Matrix.mulVec.{0, 0, 0} (Fin k) (Fin k) RankwidthDomination.Bit
          (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} RankwidthDomination.Bit
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} RankwidthDomination.Bit
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} RankwidthDomination.Bit
                (@CommRing.toNonUnitalCommRing.{0} RankwidthDomination.Bit
                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
          (Fin.fintype k) X t)
        p)
      (@Eq.{1} (Fin k → RankwidthDomination.Bit)
        (@Matrix.mulVec.{0, 0, 0} (Fin k) (Fin k) RankwidthDomination.Bit
          (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} RankwidthDomination.Bit
            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} RankwidthDomination.Bit
              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} RankwidthDomination.Bit
                (@CommRing.toNonUnitalCommRing.{0} RankwidthDomination.Bit
                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
          (Fin.fintype k) Y t)
        (@HAdd.hAdd.{0, 0, 0} (RankwidthDomination.Row k) (RankwidthDomination.Row k)
          (RankwidthDomination.Row k)
          (@instHAdd.{0} (RankwidthDomination.Row k)
            (@Pi.instAdd.{0, 0} (Fin k) (fun a => RankwidthDomination.Bit) fun i =>
              @Distrib.toAdd.{0} RankwidthDomination.Bit
                (@NonUnitalNonAssocSemiring.toDistrib.{0} RankwidthDomination.Bit
                  (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} RankwidthDomination.Bit
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} RankwidthDomination.Bit
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} RankwidthDomination.Bit
                        (@CommRing.toNonUnitalCommRing.{0} RankwidthDomination.Bit
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
          p r))) := by
  exact @RankwidthDomination.checker_no_neighbor_iff

/-- Paper 3.4; component RankwidthDomination.exactEqualityTest. -/
theorem RankwidthPaper.result_3_4_2 :
    ∀ {k : Nat} (X Y : RankwidthDomination.Assignment k),
  Iff
    (∀ (t p r : RankwidthDomination.Row k),
      @Ne.{1} (RankwidthDomination.Row k) r
          (@OfNat.ofNat.{0} (RankwidthDomination.Row k) (nat_lit 0)
            (@Zero.toOfNat0.{0} (RankwidthDomination.Row k)
              (@Pi.instZero.{0, 0} (Fin k) (fun a => RankwidthDomination.Bit) fun i =>
                @MulZeroClass.toZero.{0} RankwidthDomination.Bit
                  (@NonUnitalNonAssocSemiring.toMulZeroClass.{0} RankwidthDomination.Bit
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} RankwidthDomination.Bit
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} RankwidthDomination.Bit
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} RankwidthDomination.Bit
                          (@CommRing.toNonUnitalCommRing.{0} RankwidthDomination.Bit
                            (ZMod.commRing
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))) →
        @RankwidthDomination.checkerHasNeighbor k X Y t p r)
    (@Eq.{1} (RankwidthDomination.Assignment k) X Y) := by
  exact @RankwidthDomination.exactEqualityTest

/-- Paper 3.5; component RankwidthDomination.bounded_domination_iff. -/
theorem RankwidthPaper.result_3_5_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (s : Bool) (D : Finset.{0} (RankwidthDomination.Vertex k m)),
  Iff
    (And
      (@RankwidthDomination.Dominates.{0} (RankwidthDomination.Vertex k m)
        (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ s) D)
      (@LE.le.{0} Nat instLENat (@Finset.card.{0} (RankwidthDomination.Vertex k m) D)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          k)))
    (@Exists.{1} (RankwidthDomination.Assignment k) fun X =>
      And (@RankwidthDomination.Satisfies k m φ X)
        (@Eq.{1} (Finset.{0} (RankwidthDomination.Vertex k m)) D (@RankwidthDomination.canonical k m X))) := by
  exact @RankwidthDomination.bounded_domination_iff

/-- Paper 3.5; component RankwidthDomination.canonical_injective. -/
theorem RankwidthPaper.result_3_5_2 :
    ∀ {k m : Nat},
  @Function.Injective.{1, 1} (RankwidthDomination.Assignment k) (Finset.{0} (RankwidthDomination.Vertex k m))
    (@RankwidthDomination.canonical k m) := by
  exact @RankwidthDomination.canonical_injective

/-- Paper 3.5; component RankwidthDomination.satisfyingEquivDominating. -/
theorem RankwidthPaper.result_3_5_3 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      (s : Bool) →
        Equiv.{1, 1} (@RankwidthDomination.SatisfyingAssignments k m φ)
          (@RankwidthDomination.BoundedDominatingSets k m φ s)) := by
  exact ⟨@RankwidthDomination.satisfyingEquivDominating⟩

/-- Paper 3.5; component RankwidthDomination.boundedEquivExact. -/
theorem RankwidthPaper.result_3_5_4 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      (s : Bool) →
        Equiv.{1, 1} (@RankwidthDomination.BoundedDominatingSets k m φ s)
          (@RankwidthDomination.ExactDominatingSets k m φ s)) := by
  exact ⟨@RankwidthDomination.boundedEquivExact⟩

/-- Paper 3.5; component RankwidthDomination.basic_counts. -/
theorem RankwidthPaper.result_3_5_5 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (s : Bool),
  And
    (@Eq.{1} Nat (Nat.card.{0} (@RankwidthDomination.BoundedDominatingSets k m φ s))
      (Nat.card.{0} (@RankwidthDomination.ExactDominatingSets k m φ s)))
    (@Eq.{1} Nat (Nat.card.{0} (@RankwidthDomination.ExactDominatingSets k m φ s))
      (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ))) := by
  exact @RankwidthDomination.basic_counts

/-- Paper 3.6; component RankwidthDomination.SuppliedOrder.basic_prefix_bound. -/
theorem RankwidthPaper.result_3_6_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (n : Nat),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.cutRank.{0} (RankwidthDomination.Vertex k m)
      (@RankwidthDomination.instFintypeVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.false)
      (@RankwidthDomination.SuppliedOrder.prefixSet k m n))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  exact @RankwidthDomination.SuppliedOrder.basic_prefix_bound

/-- Paper 3.6; component RankwidthDomination.BaseTargetWidths.basic_order_width. -/
theorem RankwidthPaper.result_3_6_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.WidthParameters.VertexOrder.width.{0} (RankwidthDomination.Vertex k m)
      (@RankwidthDomination.instFintypeVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.false)
      (RankwidthDomination.WitnessEncoding.paperLabeling k m))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  exact @RankwidthDomination.BaseTargetWidths.basic_order_width

/-- Paper 3.7; component RankwidthDomination.split_partition. -/
theorem RankwidthPaper.result_3_7_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  And
    (@SimpleGraph.IsClique.{0} (RankwidthDomination.Vertex k m)
      (@RankwidthDomination.coreGraph k m φ Bool.true)
      (@setOf.{0} (RankwidthDomination.Vertex k m) fun v => @RankwidthDomination.IsChoice k m v))
    (@SimpleGraph.IsIndepSet.{0} (RankwidthDomination.Vertex k m)
      (@RankwidthDomination.coreGraph k m φ Bool.true)
      (@setOf.{0} (RankwidthDomination.Vertex k m) fun v => Not (@RankwidthDomination.IsChoice k m v))) := by
  exact @RankwidthDomination.split_partition

/-- Paper 3.7; component RankwidthDomination.SuppliedOrder.split_prefix_bound. -/
theorem RankwidthPaper.result_3_7_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (n : Nat),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.cutRank.{0} (RankwidthDomination.Vertex k m)
      (@RankwidthDomination.instFintypeVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
      (@RankwidthDomination.SuppliedOrder.prefixSet k m n))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) := by
  exact @RankwidthDomination.SuppliedOrder.split_prefix_bound

/-- Paper 3.8; component RankwidthDomination.bip_domination_card_lower_bound. -/
theorem RankwidthPaper.result_3_8_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (D : Finset.{0} (RankwidthDomination.BipVertex k m)),
  @RankwidthDomination.Dominates.{0} (RankwidthDomination.BipVertex k m)
      (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ) D →
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          k)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Finset.card.{0} (RankwidthDomination.BipVertex k m) D) := by
  exact @RankwidthDomination.bip_domination_card_lower_bound

/-- Paper 3.8; component RankwidthDomination.bip_tight_normal_form. -/
theorem RankwidthPaper.result_3_8_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (D : Finset.{0} (RankwidthDomination.BipVertex k m)),
  @RankwidthDomination.Dominates.{0} (RankwidthDomination.BipVertex k m)
      (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ) D →
    @LE.le.{0} Nat instLENat (@Finset.card.{0} (RankwidthDomination.BipVertex k m) D)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            k)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @Exists.{1}
        (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          RankwidthDomination.Assignment k)
        fun R =>
        And
          (@Eq.{1} (Finset.{0} (RankwidthDomination.BipVertex k m)) D
            (@RankwidthDomination.bipSelected k m R))
          (@Eq.{1} Nat (@Finset.card.{0} (RankwidthDomination.BipVertex k m) D)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @RankwidthDomination.bip_tight_normal_form

/-- Paper 3.9; component RankwidthDomination.bip_isBipartite. -/
theorem RankwidthPaper.result_3_9_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @SimpleGraph.IsBipartite.{0} (RankwidthDomination.BipVertex k m) (@RankwidthDomination.bipGraph k m φ) := by
  exact @RankwidthDomination.bip_isBipartite

/-- Paper 3.9; component RankwidthDomination.bip_ediameter_le_four. -/
theorem RankwidthPaper.result_3_9_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  (∀
      (h :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Finset.Nonempty.{0} (RankwidthDomination.Literal k) (φ h)) →
    @LE.le.{0} ENat
      (@Preorder.toLE.{0} ENat
        (@PartialOrder.toPreorder.{0} ENat
          (@OmegaCompletePartialOrder.toPartialOrder.{0} ENat
            (@CompleteLattice.instOmegaCompletePartialOrder.{0} ENat
              (@CompletelyDistribLattice.toCompleteLattice.{0} ENat
                (@CompleteLinearOrder.toCompletelyDistribLattice.{0} ENat instCompleteLinearOrderENat))))))
      (@SimpleGraph.ediam.{0} (RankwidthDomination.BipVertex k m) (@RankwidthDomination.bipGraph k m φ))
      (@OfNat.ofNat.{0} ENat (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} ENat (nat_lit 4) ENat.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := by
  exact @RankwidthDomination.bip_ediameter_le_four

/-- Paper 3.9; component RankwidthDomination.satisfyingEquivBipDominating. -/
theorem RankwidthPaper.result_3_9_3 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      Equiv.{1, 1} (@RankwidthDomination.SatisfyingAssignments k m φ)
        (@RankwidthDomination.BipBoundedDominatingSets k m φ)) := by
  exact ⟨@RankwidthDomination.satisfyingEquivBipDominating⟩

/-- Paper 3.9; component RankwidthDomination.bip_counts. -/
theorem RankwidthPaper.result_3_9_4 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  And
    (@Eq.{1} Nat (Nat.card.{0} (@RankwidthDomination.BipBoundedDominatingSets k m φ))
      (Nat.card.{0} (@RankwidthDomination.BipExactDominatingSets k m φ)))
    (@Eq.{1} Nat (Nat.card.{0} (@RankwidthDomination.BipExactDominatingSets k m φ))
      (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ))) := by
  exact @RankwidthDomination.bip_counts

/-- Paper 3.9; component RankwidthDomination.SuppliedOrder.bip_prefix_bound. -/
theorem RankwidthPaper.result_3_9_5 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (n : Nat),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.cutRank.{0} (RankwidthDomination.BipVertex k m)
      (@RankwidthDomination.instFintypeBipVertex k m) (@RankwidthDomination.bipGraph k m φ)
      (@setOf.{0} (RankwidthDomination.BipVertex k m) fun v =>
        @Membership.mem.{0, 0} (RankwidthDomination.BipVertex k m)
          (List.{0} (RankwidthDomination.BipVertex k m))
          (@List.instMembership.{0} (RankwidthDomination.BipVertex k m))
          (@List.take.{0} (RankwidthDomination.BipVertex k m) n
            (RankwidthDomination.SuppliedOrder.bipVertices k m))
          v))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) := by
  exact @RankwidthDomination.SuppliedOrder.bip_prefix_bound

/-- Paper 3.10; component RankwidthDomination.MainResults.corollary_3_10. -/
theorem RankwidthPaper.result_3_10_1 :
    RankwidthDomination.Complexity.ETH →
  ∀ (cl : RankwidthDomination.GraphProblem.GraphClass),
    RankwidthDomination.MainResults.DominationClass cl →
      And
        (Not
          (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
            RankwidthDomination.GraphProblem.Problem.domination cl
            RankwidthDomination.GraphProblem.Parameter.rankWidth
            RankwidthDomination.GraphProblem.Goal.decision))
        (And
          (Not
            (RankwidthDomination.WitnessedRankWidth.HasRankWidthAlgorithm
              RankwidthDomination.GraphProblem.Problem.domination cl
              RankwidthDomination.WitnessedRankWidth.WitnessMode.order
              RankwidthDomination.GraphProblem.Goal.decision))
          (Not
            (RankwidthDomination.WitnessedRankWidth.HasRankWidthAlgorithm
              RankwidthDomination.GraphProblem.Problem.domination cl
              RankwidthDomination.WitnessedRankWidth.WitnessMode.decomposition
              RankwidthDomination.GraphProblem.Goal.decision))) := by
  exact @RankwidthDomination.MainResults.corollary_3_10

/-- Paper 4.1; component RankwidthDomination.MainResults.theorem_4_1. -/
theorem RankwidthPaper.result_4_1_1 :
    RankwidthDomination.Complexity.ETH →
  ∀ (p : RankwidthDomination.GraphProblem.Parameter),
    And
      (Not
        (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
          RankwidthDomination.GraphProblem.Problem.independent
          RankwidthDomination.GraphProblem.GraphClass.monopolar p
          RankwidthDomination.GraphProblem.Goal.decision))
      (And
        (Not
          (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
            RankwidthDomination.GraphProblem.Problem.connected
            RankwidthDomination.GraphProblem.GraphClass.split p
            RankwidthDomination.GraphProblem.Goal.decision))
        (And
          (Not
            (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
              RankwidthDomination.GraphProblem.Problem.connected
              RankwidthDomination.GraphProblem.GraphClass.bipartiteDiameterFour p
              RankwidthDomination.GraphProblem.Goal.decision))
          (And
            (Not
              (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
                RankwidthDomination.GraphProblem.Problem.total
                RankwidthDomination.GraphProblem.GraphClass.split p
                RankwidthDomination.GraphProblem.Goal.decision))
            (Not
              (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
                RankwidthDomination.GraphProblem.Problem.total
                RankwidthDomination.GraphProblem.GraphClass.bipartiteDiameterFour p
                RankwidthDomination.GraphProblem.Goal.decision))))) := by
  exact @RankwidthDomination.MainResults.theorem_4_1

/-- Paper 4.2; component RankwidthDomination.MainResults.theorem_4_2. -/
theorem RankwidthPaper.result_4_2_1 :
    RankwidthDomination.Complexity.CountingETH →
  ∀ (p : RankwidthDomination.GraphProblem.Parameter) (goal : RankwidthDomination.GraphProblem.Goal),
    @Ne.{1} RankwidthDomination.GraphProblem.Goal goal RankwidthDomination.GraphProblem.Goal.decision →
      And
        (Not
          (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
            RankwidthDomination.GraphProblem.Problem.independent
            RankwidthDomination.GraphProblem.GraphClass.monopolar p goal))
        (And
          (Not
            (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
              RankwidthDomination.GraphProblem.Problem.connected
              RankwidthDomination.GraphProblem.GraphClass.split p goal))
          (And
            (Not
              (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
                RankwidthDomination.GraphProblem.Problem.connected
                RankwidthDomination.GraphProblem.GraphClass.bipartiteDiameterFour p goal))
            (And
              (Not
                (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
                  RankwidthDomination.GraphProblem.Problem.total
                  RankwidthDomination.GraphProblem.GraphClass.split p goal))
              (Not
                (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
                  RankwidthDomination.GraphProblem.Problem.total
                  RankwidthDomination.GraphProblem.GraphClass.bipartiteDiameterFour p goal))))) := by
  exact @RankwidthDomination.MainResults.theorem_4_2

/-- Paper 4.3; component RankwidthDomination.canonical_independent. -/
theorem RankwidthPaper.result_4_3_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (X : RankwidthDomination.Assignment k),
  @SimpleGraph.IsIndepSet.{0} (RankwidthDomination.Vertex k m)
    (@RankwidthDomination.coreGraph k m φ Bool.false)
    (@Finset.toSet.{0} (RankwidthDomination.Vertex k m) (@RankwidthDomination.canonical k m X)) := by
  exact @RankwidthDomination.canonical_independent

/-- Paper 4.3; component RankwidthDomination.canonical_split_clique. -/
theorem RankwidthPaper.result_4_3_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (X : RankwidthDomination.Assignment k),
  @SimpleGraph.IsClique.{0} (RankwidthDomination.Vertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
    (@Finset.toSet.{0} (RankwidthDomination.Vertex k m) (@RankwidthDomination.canonical k m X)) := by
  exact @RankwidthDomination.canonical_split_clique

/-- Paper 4.3; component RankwidthDomination.canonical_split_connected. -/
theorem RankwidthPaper.result_4_3_3 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (X : RankwidthDomination.Assignment k),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    @RankwidthDomination.ConnectedSelected.{0} (RankwidthDomination.Vertex k m)
      (@RankwidthDomination.coreGraph k m φ Bool.true) (@RankwidthDomination.canonical k m X) := by
  exact @RankwidthDomination.canonical_split_connected

/-- Paper 4.3; component RankwidthDomination.canonical_split_total. -/
theorem RankwidthPaper.result_4_3_4 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (X : RankwidthDomination.Assignment k),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        k) →
    @RankwidthDomination.Satisfies k m φ X →
      @RankwidthDomination.TotalDominates.{0} (RankwidthDomination.Vertex k m)
        (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
        (@RankwidthDomination.canonical k m X) := by
  exact @RankwidthDomination.canonical_split_total

/-- Paper 4.3; component RankwidthDomination.bipCanonical_star. -/
theorem RankwidthPaper.result_4_3_5 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (X : RankwidthDomination.Assignment k)
  (u v : RankwidthDomination.BipVertex k m),
  @Membership.mem.{0, 0} (RankwidthDomination.BipVertex k m) (Finset.{0} (RankwidthDomination.BipVertex k m))
      (@Finset.instMembership.{0} (RankwidthDomination.BipVertex k m))
      (@RankwidthDomination.bipCanonical k m X) u →
    @Membership.mem.{0, 0} (RankwidthDomination.BipVertex k m)
        (Finset.{0} (RankwidthDomination.BipVertex k m))
        (@Finset.instMembership.{0} (RankwidthDomination.BipVertex k m))
        (@RankwidthDomination.bipCanonical k m X) v →
      Iff (@SimpleGraph.Adj.{0} (RankwidthDomination.BipVertex k m) (@RankwidthDomination.bipGraph k m φ) u v)
        (Or
          (And (@Eq.{1} (RankwidthDomination.BipVertex k m) u (@RankwidthDomination.BipVertex.hub k m))
            (@Ne.{1} (RankwidthDomination.BipVertex k m) v (@RankwidthDomination.BipVertex.hub k m)))
          (And (@Eq.{1} (RankwidthDomination.BipVertex k m) v (@RankwidthDomination.BipVertex.hub k m))
            (@Ne.{1} (RankwidthDomination.BipVertex k m) u (@RankwidthDomination.BipVertex.hub k m)))) := by
  exact @RankwidthDomination.bipCanonical_star

/-- Paper 4.3; component RankwidthDomination.bipCanonical_connected. -/
theorem RankwidthPaper.result_4_3_6 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (X : RankwidthDomination.Assignment k),
  @RankwidthDomination.ConnectedSelected.{0} (RankwidthDomination.BipVertex k m)
    (@RankwidthDomination.bipGraph k m φ) (@RankwidthDomination.bipCanonical k m X) := by
  exact @RankwidthDomination.bipCanonical_connected

/-- Paper 4.3; component RankwidthDomination.bipCanonical_total. -/
theorem RankwidthPaper.result_4_3_7 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (X : RankwidthDomination.Assignment k),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    @RankwidthDomination.Satisfies k m φ X →
      @RankwidthDomination.TotalDominates.{0} (RankwidthDomination.BipVertex k m)
        (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)
        (@RankwidthDomination.bipCanonical k m X) := by
  exact @RankwidthDomination.bipCanonical_total

/-- Paper 4.4; component RankwidthDomination.satisfyingEquivIndependent. -/
theorem RankwidthPaper.result_4_4_1 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      Equiv.{1, 1} (@RankwidthDomination.SatisfyingAssignments k m φ)
        (@RankwidthDomination.BoundedVariantSets.{0} (RankwidthDomination.Vertex k m)
          (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.false)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            k)
          fun D =>
          @SimpleGraph.IsIndepSet.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.coreGraph k m φ Bool.false)
            (@Finset.toSet.{0} (RankwidthDomination.Vertex k m) D))) := by
  exact ⟨@RankwidthDomination.satisfyingEquivIndependent⟩

/-- Paper 4.4; component RankwidthDomination.independent_counts. -/
theorem RankwidthPaper.result_4_4_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  And
    (@Eq.{1} Nat
      (Nat.card.{0}
        (@RankwidthDomination.BoundedVariantSets.{0} (RankwidthDomination.Vertex k m)
          (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.false)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            k)
          fun D =>
          @SimpleGraph.IsIndepSet.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.coreGraph k m φ Bool.false)
            (@Finset.toSet.{0} (RankwidthDomination.Vertex k m) D)))
      (Nat.card.{0}
        (@RankwidthDomination.ExactVariantSets.{0} (RankwidthDomination.Vertex k m)
          (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.false)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            k)
          fun D =>
          @SimpleGraph.IsIndepSet.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.coreGraph k m φ Bool.false)
            (@Finset.toSet.{0} (RankwidthDomination.Vertex k m) D))))
    (@Eq.{1} Nat
      (Nat.card.{0}
        (@RankwidthDomination.ExactVariantSets.{0} (RankwidthDomination.Vertex k m)
          (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.false)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            k)
          fun D =>
          @SimpleGraph.IsIndepSet.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.coreGraph k m φ Bool.false)
            (@Finset.toSet.{0} (RankwidthDomination.Vertex k m) D)))
      (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ))) := by
  exact @RankwidthDomination.independent_counts

/-- Paper 4.5; component RankwidthDomination.satisfyingEquivSplitConnected. -/
theorem RankwidthPaper.result_4_5_1 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
        Equiv.{1, 1} (@RankwidthDomination.SatisfyingAssignments k m φ)
          (@RankwidthDomination.BoundedVariantSets.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@RankwidthDomination.ConnectedSelected.{0} (RankwidthDomination.Vertex k m)
              (@RankwidthDomination.coreGraph k m φ Bool.true)))) := by
  exact ⟨@RankwidthDomination.satisfyingEquivSplitConnected⟩

/-- Paper 4.5; component RankwidthDomination.satisfyingEquivSplitTotal. -/
theorem RankwidthPaper.result_4_5_2 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            k) →
        Equiv.{1, 1} (@RankwidthDomination.SatisfyingAssignments k m φ)
          (@RankwidthDomination.BoundedVariantSets.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@RankwidthDomination.TotalDominates.{0} (RankwidthDomination.Vertex k m)
              (@RankwidthDomination.instDecidableEqVertex k m)
              (@RankwidthDomination.coreGraph k m φ Bool.true)))) := by
  exact ⟨@RankwidthDomination.satisfyingEquivSplitTotal⟩

/-- Paper 4.5; component RankwidthDomination.split_connected_counts. -/
theorem RankwidthPaper.result_4_5_3 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    And
      (@Eq.{1} Nat
        (Nat.card.{0}
          (@RankwidthDomination.BoundedVariantSets.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@RankwidthDomination.ConnectedSelected.{0} (RankwidthDomination.Vertex k m)
              (@RankwidthDomination.coreGraph k m φ Bool.true))))
        (Nat.card.{0}
          (@RankwidthDomination.ExactVariantSets.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@RankwidthDomination.ConnectedSelected.{0} (RankwidthDomination.Vertex k m)
              (@RankwidthDomination.coreGraph k m φ Bool.true)))))
      (@Eq.{1} Nat
        (Nat.card.{0}
          (@RankwidthDomination.ExactVariantSets.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@RankwidthDomination.ConnectedSelected.{0} (RankwidthDomination.Vertex k m)
              (@RankwidthDomination.coreGraph k m φ Bool.true))))
        (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ))) := by
  exact @RankwidthDomination.split_connected_counts

/-- Paper 4.5; component RankwidthDomination.split_total_counts. -/
theorem RankwidthPaper.result_4_5_4 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        k) →
    And
      (@Eq.{1} Nat
        (Nat.card.{0}
          (@RankwidthDomination.BoundedVariantSets.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@RankwidthDomination.TotalDominates.{0} (RankwidthDomination.Vertex k m)
              (@RankwidthDomination.instDecidableEqVertex k m)
              (@RankwidthDomination.coreGraph k m φ Bool.true))))
        (Nat.card.{0}
          (@RankwidthDomination.ExactVariantSets.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@RankwidthDomination.TotalDominates.{0} (RankwidthDomination.Vertex k m)
              (@RankwidthDomination.instDecidableEqVertex k m)
              (@RankwidthDomination.coreGraph k m φ Bool.true)))))
      (@Eq.{1} Nat
        (Nat.card.{0}
          (@RankwidthDomination.ExactVariantSets.{0} (RankwidthDomination.Vertex k m)
            (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ Bool.true)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@RankwidthDomination.TotalDominates.{0} (RankwidthDomination.Vertex k m)
              (@RankwidthDomination.instDecidableEqVertex k m)
              (@RankwidthDomination.coreGraph k m φ Bool.true))))
        (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ))) := by
  exact @RankwidthDomination.split_total_counts

/-- Paper 4.6; component RankwidthDomination.satisfyingEquivBipConnected. -/
theorem RankwidthPaper.result_4_6_1 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      Equiv.{1, 1} (@RankwidthDomination.SatisfyingAssignments k m φ)
        (@RankwidthDomination.BoundedVariantSets.{0} (RankwidthDomination.BipVertex k m)
          (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@RankwidthDomination.ConnectedSelected.{0} (RankwidthDomination.BipVertex k m)
            (@RankwidthDomination.bipGraph k m φ)))) := by
  exact ⟨@RankwidthDomination.satisfyingEquivBipConnected⟩

/-- Paper 4.6; component RankwidthDomination.satisfyingEquivBipTotal. -/
theorem RankwidthPaper.result_4_6_2 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
        Equiv.{1, 1} (@RankwidthDomination.SatisfyingAssignments k m φ)
          (@RankwidthDomination.BoundedVariantSets.{0} (RankwidthDomination.BipVertex k m)
            (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@RankwidthDomination.TotalDominates.{0} (RankwidthDomination.BipVertex k m)
              (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)))) := by
  exact ⟨@RankwidthDomination.satisfyingEquivBipTotal⟩

/-- Paper 4.6; component RankwidthDomination.bip_connected_counts. -/
theorem RankwidthPaper.result_4_6_3 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  And
    (@Eq.{1} Nat
      (Nat.card.{0}
        (@RankwidthDomination.BoundedVariantSets.{0} (RankwidthDomination.BipVertex k m)
          (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@RankwidthDomination.ConnectedSelected.{0} (RankwidthDomination.BipVertex k m)
            (@RankwidthDomination.bipGraph k m φ))))
      (Nat.card.{0}
        (@RankwidthDomination.ExactVariantSets.{0} (RankwidthDomination.BipVertex k m)
          (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@RankwidthDomination.ConnectedSelected.{0} (RankwidthDomination.BipVertex k m)
            (@RankwidthDomination.bipGraph k m φ)))))
    (@Eq.{1} Nat
      (Nat.card.{0}
        (@RankwidthDomination.ExactVariantSets.{0} (RankwidthDomination.BipVertex k m)
          (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@RankwidthDomination.ConnectedSelected.{0} (RankwidthDomination.BipVertex k m)
            (@RankwidthDomination.bipGraph k m φ))))
      (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ))) := by
  exact @RankwidthDomination.bip_connected_counts

/-- Paper 4.6; component RankwidthDomination.bip_total_counts. -/
theorem RankwidthPaper.result_4_6_4 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    And
      (@Eq.{1} Nat
        (Nat.card.{0}
          (@RankwidthDomination.BoundedVariantSets.{0} (RankwidthDomination.BipVertex k m)
            (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@RankwidthDomination.TotalDominates.{0} (RankwidthDomination.BipVertex k m)
              (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ))))
        (Nat.card.{0}
          (@RankwidthDomination.ExactVariantSets.{0} (RankwidthDomination.BipVertex k m)
            (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@RankwidthDomination.TotalDominates.{0} (RankwidthDomination.BipVertex k m)
              (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)))))
      (@Eq.{1} Nat
        (Nat.card.{0}
          (@RankwidthDomination.ExactVariantSets.{0} (RankwidthDomination.BipVertex k m)
            (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@RankwidthDomination.TotalDominates.{0} (RankwidthDomination.BipVertex k m)
              (@RankwidthDomination.instDecidableEqBipVertex k m) (@RankwidthDomination.bipGraph k m φ))))
        (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ))) := by
  exact @RankwidthDomination.bip_total_counts

/-- Paper 5.1; component RankwidthDomination.MainResults.theorem_5_1_independent. -/
theorem RankwidthPaper.result_5_1_1 :
    ∀ (σ ρ : Set.{0} Nat),
  @Set.Finite.{0} Nat (@HasCompl.compl.{0} (Set.{0} Nat) (@Set.instHasCompl.{0} Nat) ρ) →
    Not
        (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) σ
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          ∀ (p : RankwidthDomination.GraphProblem.Parameter),
            And
              (RankwidthDomination.Complexity.ETH →
                Not
                  (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
                    (RankwidthDomination.GraphProblem.Problem.sigmaRho σ ρ)
                    RankwidthDomination.GraphProblem.GraphClass.monopolar p
                    RankwidthDomination.GraphProblem.Goal.decision))
              (RankwidthDomination.Complexity.CountingETH →
                ∀ (goal : RankwidthDomination.GraphProblem.Goal),
                  @Ne.{1} RankwidthDomination.GraphProblem.Goal goal
                      RankwidthDomination.GraphProblem.Goal.decision →
                    Not
                      (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
                        (RankwidthDomination.GraphProblem.Problem.sigmaRho σ ρ)
                        RankwidthDomination.GraphProblem.GraphClass.monopolar p goal)) := by
  exact @RankwidthDomination.MainResults.theorem_5_1_independent

/-- Paper 5.1; component RankwidthDomination.MainResults.theorem_5_1_cofinite. -/
theorem RankwidthPaper.result_5_1_2 :
    ∀ (σ ρ : Set.{0} Nat),
  @Set.Finite.{0} Nat (@HasCompl.compl.{0} (Set.{0} Nat) (@Set.instHasCompl.{0} Nat) σ) →
    @Set.Finite.{0} Nat (@HasCompl.compl.{0} (Set.{0} Nat) (@Set.instHasCompl.{0} Nat) ρ) →
      Not
          (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
        ∀ (p : RankwidthDomination.GraphProblem.Parameter),
          And
            (RankwidthDomination.Complexity.ETH →
              Not
                (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
                  (RankwidthDomination.GraphProblem.Problem.sigmaRho σ ρ)
                  RankwidthDomination.GraphProblem.GraphClass.split p
                  RankwidthDomination.GraphProblem.Goal.decision))
            (RankwidthDomination.Complexity.CountingETH →
              ∀ (goal : RankwidthDomination.GraphProblem.Goal),
                @Ne.{1} RankwidthDomination.GraphProblem.Goal goal
                    RankwidthDomination.GraphProblem.Goal.decision →
                  Not
                    (RankwidthDomination.GraphProblem.HasSubquadraticAlgorithm
                      (RankwidthDomination.GraphProblem.Problem.sigmaRho σ ρ)
                      RankwidthDomination.GraphProblem.GraphClass.split p goal)) := by
  exact @RankwidthDomination.MainResults.theorem_5_1_cofinite

/-- Paper 5.1; component RankwidthDomination.CompleteFamilyTargetPipeline.sigmaMachine_correct. -/
theorem RankwidthPaper.result_5_1_3 :
    ∀ {k m b : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    ∀
      (f :
        RankwidthDomination.Padding.FlatCNF
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (hlen :
        @Eq.{1} Nat
          (@List.length.{0}
            (RankwidthDomination.Padding.FlatClause
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            f)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (clique : Bool) (P Q : Finset.{0} (Fin b)) (R : Fin b → Finset.{0} (Fin b))
      (p : RankwidthDomination.GraphProblem.Parameter),
      (@RankwidthDomination.CompleteFamilyTargetPipeline.sigmaMachine b clique P Q R p).outputsInTime
        (@RankwidthDomination.Padding.BinaryEncoding.formulaBits
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          f)
        (@RankwidthDomination.CompleteFamilyTargetPipeline.sigmaTarget k m b
          (@RankwidthDomination.Padding.matrixCNF k m f hlen) clique P Q R p)
        (@RankwidthDomination.CompleteFamilyTargetPipeline.sigmaBound k m b f hlen clique P Q R p) := by
  exact @RankwidthDomination.CompleteFamilyTargetPipeline.sigmaMachine_correct

/-- Paper 5.2; component RankwidthDomination.SigmaConstruction.tight_normal_form. -/
theorem RankwidthPaper.result_5_2_1 :
    ∀ {k m b : Nat} (φ : RankwidthDomination.CNF k m) (clique : Bool) (P Q : Finset.{0} (Fin b))
  (R : Fin b → Finset.{0} (Fin b)) (r : Nat),
  (∀ (u : Fin b),
      @Membership.mem.{0, 0} (Fin b) (Finset.{0} (Fin b)) (@Finset.instMembership.{0} (Fin b)) (R u) u) →
    (∀ (u : Fin b), @Eq.{1} Nat (@Finset.card.{0} (Fin b) (R u)) r) →
      @LT.lt.{0} Nat instLTNat (@Finset.card.{0} (Fin b) P) r →
        ∀ (σ ρ : Set.{0} Nat),
          (∀ (n : Nat),
              @LT.lt.{0} Nat instLTNat n r →
                Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ n)) →
            ∀ (S : Finset.{0} (RankwidthDomination.SigmaConstruction.V k m b)),
              @RankwidthDomination.IsSigmaRho.{0} (RankwidthDomination.SigmaConstruction.V k m b)
                  (fun a b_1 =>
                    @instDecidableEqSum.{0, 0} (RankwidthDomination.Vertex k m)
                      (RankwidthDomination.ReservoirVertex.{0} (Fin b))
                      (@RankwidthDomination.instDecidableEqVertex k m)
                      (fun a b_2 =>
                        @instDecidableEqSum.{0, 0} (Fin b) (Prod.{0, 0} (Fin b) Bool) (instDecidableEqFin b)
                          (fun a b_3 =>
                            @instDecidableEqProd.{0, 0} (Fin b) Bool (instDecidableEqFin b)
                              instDecidableEqBool a b_3)
                          a b_2)
                      a b_1)
                  (@RankwidthDomination.SigmaConstruction.graph k m b φ clique P Q R)
                  (@RankwidthDomination.SigmaConstruction.instDecidableRelVAdjGraph k m b φ clique P Q R) σ ρ
                  S →
                @LE.le.{0} Nat instLENat (@Finset.card.{0} (RankwidthDomination.SigmaConstruction.V k m b) S)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        k)) →
                  @Exists.{1}
                    (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      RankwidthDomination.Assignment k)
                    fun T =>
                    And
                      (@Eq.{1} (Finset.{0} (RankwidthDomination.SigmaConstruction.V k m b)) S
                        (@RankwidthDomination.SigmaConstruction.selectedAll k m b T))
                      (@Eq.{1} Nat (@Finset.card.{0} (RankwidthDomination.SigmaConstruction.V k m b) S)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            k))) := by
  exact @RankwidthDomination.SigmaConstruction.tight_normal_form

/-- Paper 5.3; component RankwidthDomination.SigmaConstruction.satisfyingEquivSolutions. -/
theorem RankwidthPaper.result_5_3_1 :
    Nonempty.{1}
  ({k m b : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      (clique : Bool) →
        (P Q : Finset.{0} (Fin b)) →
          (R : Fin b → Finset.{0} (Fin b)) →
            (r : Nat) →
              (∀ (u : Fin b),
                  @Membership.mem.{0, 0} (Fin b) (Finset.{0} (Fin b)) (@Finset.instMembership.{0} (Fin b))
                    (R u) u) →
                (∀ (u : Fin b), @Eq.{1} Nat (@Finset.card.{0} (Fin b) (R u)) r) →
                  @LT.lt.{0} Nat instLTNat (@Finset.card.{0} (Fin b) P) r →
                    (σ ρ : Set.{0} Nat) →
                      (∀ (n : Nat),
                          @LT.lt.{0} Nat instLTNat n r →
                            Not
                              (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ n)) →
                        (q : Nat) →
                          @Eq.{1} Nat (@Finset.card.{0} (Fin b) Q) q →
                            Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ q) →
                              (∀ (n : Nat),
                                  @LT.lt.{0} Nat instLTNat q n →
                                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
                                      n) →
                                @ite.{1} Prop (@Eq.{1} Bool clique Bool.true)
                                    (instDecidableEqBool clique Bool.true)
                                    (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) σ
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            k))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) σ
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                                  @ite.{1} Prop (@Eq.{1} Bool clique Bool.true)
                                      (instDecidableEqBool clique Bool.true)
                                      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                                        ρ
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            k)))
                                      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                                        ρ (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Finset.card.{0} (Fin b) P)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                      (∀ (u : Fin b),
                                          @Membership.mem.{0, 0} Nat (Set.{0} Nat)
                                            (@Set.instMembership.{0} Nat) ρ
                                            (@Finset.card.{0} (Fin b) (R u))) →
                                        Equiv.{1, 1} (@RankwidthDomination.SatisfyingAssignments k m φ)
                                          (@RankwidthDomination.SigmaConstruction.BoundedSolutions k m b φ
                                            clique P Q R σ ρ)) := by
  exact ⟨@RankwidthDomination.SigmaConstruction.satisfyingEquivSolutions⟩

/-- Paper 5.3; component RankwidthDomination.SigmaConstruction.independent_counts. -/
theorem RankwidthPaper.result_5_3_2 :
    ∀ {k m b : Nat} (φ : RankwidthDomination.CNF k m) (σ ρ : Set.{0} Nat),
  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) σ
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    Not
        (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        ∀ (q : Nat),
          Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ q) →
            (∀ (n : Nat),
                @LT.lt.{0} Nat instLTNat q n →
                  @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ n) →
              ∀ (Q : Finset.{0} (Fin b)),
                @Eq.{1} Nat (@Finset.card.{0} (Fin b) Q) q →
                  And
                    (@Eq.{1} Nat
                      (Nat.card.{0}
                        (@RankwidthDomination.SigmaConstruction.BoundedSolutions k m b φ Bool.false
                          (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin b))
                            (@Finset.instEmptyCollection.{0} (Fin b)))
                          Q
                          (fun u =>
                            @Singleton.singleton.{0, 0} (Fin b) (Finset.{0} (Fin b))
                              (@Finset.instSingleton.{0} (Fin b)) u)
                          σ ρ))
                      (Nat.card.{0}
                        (@RankwidthDomination.SigmaConstruction.ExactSolutions k m b φ Bool.false
                          (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin b))
                            (@Finset.instEmptyCollection.{0} (Fin b)))
                          Q
                          (fun u =>
                            @Singleton.singleton.{0, 0} (Fin b) (Finset.{0} (Fin b))
                              (@Finset.instSingleton.{0} (Fin b)) u)
                          σ ρ)))
                    (@Eq.{1} Nat
                      (Nat.card.{0}
                        (@RankwidthDomination.SigmaConstruction.ExactSolutions k m b φ Bool.false
                          (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin b))
                            (@Finset.instEmptyCollection.{0} (Fin b)))
                          Q
                          (fun u =>
                            @Singleton.singleton.{0, 0} (Fin b) (Finset.{0} (Fin b))
                              (@Finset.instSingleton.{0} (Fin b)) u)
                          σ ρ))
                      (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ))) := by
  exact @RankwidthDomination.SigmaConstruction.independent_counts

/-- Paper 5.3; component RankwidthDomination.SigmaConstruction.independent_branch_exists. -/
theorem RankwidthPaper.result_5_3_3 :
    ∀ (σ ρ : Set.{0} Nat),
  @Set.Finite.{0} Nat (@HasCompl.compl.{0} (Set.{0} Nat) (@Set.instHasCompl.{0} Nat) ρ) →
    Not
        (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) σ
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Exists.{1} Nat fun b =>
            @Exists.{1} (Finset.{0} (Fin b)) fun Q =>
              And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) b)
                (∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
                  And
                    (@Eq.{1} Nat
                      (Nat.card.{0}
                        (@RankwidthDomination.SigmaConstruction.BoundedSolutions k m b φ Bool.false
                          (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin b))
                            (@Finset.instEmptyCollection.{0} (Fin b)))
                          Q
                          (fun u =>
                            @Singleton.singleton.{0, 0} (Fin b) (Finset.{0} (Fin b))
                              (@Finset.instSingleton.{0} (Fin b)) u)
                          σ ρ))
                      (Nat.card.{0}
                        (@RankwidthDomination.SigmaConstruction.ExactSolutions k m b φ Bool.false
                          (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin b))
                            (@Finset.instEmptyCollection.{0} (Fin b)))
                          Q
                          (fun u =>
                            @Singleton.singleton.{0, 0} (Fin b) (Finset.{0} (Fin b))
                              (@Finset.instSingleton.{0} (Fin b)) u)
                          σ ρ)))
                    (@Eq.{1} Nat
                      (Nat.card.{0}
                        (@RankwidthDomination.SigmaConstruction.ExactSolutions k m b φ Bool.false
                          (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin b))
                            (@Finset.instEmptyCollection.{0} (Fin b)))
                          Q
                          (fun u =>
                            @Singleton.singleton.{0, 0} (Fin b) (Finset.{0} (Fin b))
                              (@Finset.instSingleton.{0} (Fin b)) u)
                          σ ρ))
                      (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ)))) := by
  exact @RankwidthDomination.SigmaConstruction.independent_branch_exists

/-- Paper 5.4; component RankwidthDomination.SigmaWidth.independent_prefix_bound. -/
theorem RankwidthPaper.result_5_4_1 :
    ∀ {k m b : Nat} (φ : RankwidthDomination.CNF k m) (Q : Finset.{0} (Fin b)) (R : Fin b → Finset.{0} (Fin b))
  (n : Nat),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.cutRank.{0} (RankwidthDomination.SigmaConstruction.V k m b)
      (@instFintypeSum.{0, 0} (RankwidthDomination.Vertex k m)
        (RankwidthDomination.ReservoirVertex.{0} (Fin b)) (@RankwidthDomination.instFintypeVertex k m)
        (@instFintypeSum.{0, 0} (Fin b) (Prod.{0, 0} (Fin b) Bool) (Fin.fintype b)
          (@instFintypeProd.{0, 0} (Fin b) Bool (Fin.fintype b) Bool.fintype)))
      (@RankwidthDomination.SigmaConstruction.graph k m b φ Bool.false
        (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin b)) (@Finset.instEmptyCollection.{0} (Fin b)))
        Q R)
      (@RankwidthDomination.SigmaWidth.listPrefix.{0} (RankwidthDomination.SigmaConstruction.V k m b)
        (RankwidthDomination.SigmaWidth.vertices k m b) n))
    (@Max.max.{0} Nat Nat.instMax
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) := by
  exact @RankwidthDomination.SigmaWidth.independent_prefix_bound

/-- Paper 5.5; component RankwidthDomination.reservoir_lower_bound. -/
theorem RankwidthPaper.result_5_5_1.{u_1, u_2} :
    ∀ {U : Type u_1} {V : Type u_2} [inst : Fintype.{u_1} U] [DecidableEq.{u_1 + 1} U]
  [inst_2 : DecidableEq.{u_2 + 1} V] (G : SimpleGraph.{u_2} V)
  [inst_3 : @DecidableRel.{u_2 + 1, u_2 + 1} V V (@SimpleGraph.Adj.{u_2} V G)]
  (e : Function.Embedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U) V)
  (R : U → Finset.{u_1} U) (r : Nat),
  (∀ (u : U), @Membership.mem.{u_1, u_1} U (Finset.{u_1} U) (@Finset.instMembership.{u_1} U) (R u) u) →
    (∀ (u : U), @Eq.{1} Nat (@Finset.card.{u_1} U (R u)) r) →
      (∀ (u : U) (i : Bool) (v : V),
          Iff
            (@SimpleGraph.Adj.{u_2} V G
              (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                (Function.Embedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
                (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1}
                  (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                e (@Sum.inr.{u_1, u_1} U (Prod.{u_1, 0} U Bool) (@Prod.mk.{u_1, 0} U Bool u i)))
              v)
            (@Exists.{u_1 + 1} U fun w =>
              And (@Membership.mem.{u_1, u_1} U (Finset.{u_1} U) (@Finset.instMembership.{u_1} U) (R u) w)
                (@Eq.{u_2 + 1} V
                  (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                    (Function.Embedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                    (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
                    (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1}
                      (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                    e (@Sum.inl.{u_1, u_1} U (Prod.{u_1, 0} U Bool) w))
                  v))) →
        ∀ (σ ρ : Set.{0} Nat),
          (∀ (n : Nat),
              @LT.lt.{0} Nat instLTNat n r →
                Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ n)) →
            ∀ (S : Finset.{u_2} V),
              @RankwidthDomination.IsSigmaRho.{u_2} V inst_2 G inst_3 σ ρ S →
                @LE.le.{0} Nat instLENat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@Fintype.card.{u_1} U inst)
                    (@Finset.card.{u_1} U
                      (@Finset.filter.{u_1} U
                        (fun u =>
                          Not
                            (@Membership.mem.{u_2, u_2} V (Finset.{u_2} V) (@Finset.instMembership.{u_2} V) S
                              (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                                (Function.Embedding.{u_1 + 1, u_2 + 1}
                                  (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                                (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
                                (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1}
                                  (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                                e (@Sum.inl.{u_1, u_1} U (Prod.{u_1, 0} U Bool) u))))
                        (fun a =>
                          @instDecidableNot
                            (@Membership.mem.{u_2, u_2} V (Finset.{u_2} V) (@Finset.instMembership.{u_2} V) S
                              (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                                (Function.Embedding.{u_1 + 1, u_2 + 1}
                                  (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                                (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
                                (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1}
                                  (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                                e (@Sum.inl.{u_1, u_1} U (Prod.{u_1, 0} U Bool) a)))
                            (@Finset.decidableMem.{u_2} V inst_2
                              (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                                (Function.Embedding.{u_1 + 1, u_2 + 1}
                                  (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                                (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
                                (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1}
                                  (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                                e (@Sum.inl.{u_1, u_1} U (Prod.{u_1, 0} U Bool) a))
                              S))
                        (@Finset.univ.{u_1} U inst))))
                  (@Finset.card.{u_2} V
                    (@Inter.inter.{u_2} (Finset.{u_2} V) (@Finset.instInter.{u_2} V inst_2) S
                      (@Finset.image.{u_1, u_2} (RankwidthDomination.ReservoirVertex.{u_1} U) V inst_2
                        (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                          (Function.Embedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U)
                            V)
                          (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
                          (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1}
                            (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                          e)
                        (@Finset.univ.{u_1} (RankwidthDomination.ReservoirVertex.{u_1} U)
                          (@instFintypeSum.{u_1, u_1} U (Prod.{u_1, 0} U Bool) inst
                            (@instFintypeProd.{u_1, 0} U Bool inst Bool.fintype)))))) := by
  exact @RankwidthDomination.reservoir_lower_bound

/-- Paper 5.5; component RankwidthDomination.reservoir_tight_iff. -/
theorem RankwidthPaper.result_5_5_2.{u_1, u_2} :
    ∀ {U : Type u_1} {V : Type u_2} [inst : Fintype.{u_1} U] [DecidableEq.{u_1 + 1} U]
  [inst_2 : DecidableEq.{u_2 + 1} V]
  (e : Function.Embedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U) V)
  (S : Finset.{u_2} V),
  (∀ (u : U),
      Not
          (@Membership.mem.{u_2, u_2} V (Finset.{u_2} V) (@Finset.instMembership.{u_2} V) S
            (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
              (Function.Embedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U) V)
              (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
              (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U)
                V)
              e (@Sum.inl.{u_1, u_1} U (Prod.{u_1, 0} U Bool) u))) →
        ∀ (i : Bool),
          @Membership.mem.{u_2, u_2} V (Finset.{u_2} V) (@Finset.instMembership.{u_2} V) S
            (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
              (Function.Embedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U) V)
              (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
              (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U)
                V)
              e (@Sum.inr.{u_1, u_1} U (Prod.{u_1, 0} U Bool) (@Prod.mk.{u_1, 0} U Bool u i)))) →
    Iff
      (@Eq.{1} Nat
        (@Finset.card.{u_2} V
          (@Inter.inter.{u_2} (Finset.{u_2} V) (@Finset.instInter.{u_2} V inst_2) S
            (@Finset.image.{u_1, u_2} (RankwidthDomination.ReservoirVertex.{u_1} U) V inst_2
              (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                (Function.Embedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
                (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1}
                  (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                e)
              (@Finset.univ.{u_1} (RankwidthDomination.ReservoirVertex.{u_1} U)
                (@instFintypeSum.{u_1, u_1} U (Prod.{u_1, 0} U Bool) inst
                  (@instFintypeProd.{u_1, 0} U Bool inst Bool.fintype))))))
        (@Fintype.card.{u_1} U inst))
      (And
        (∀ (u : U),
          @Membership.mem.{u_2, u_2} V (Finset.{u_2} V) (@Finset.instMembership.{u_2} V) S
            (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
              (Function.Embedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U) V)
              (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
              (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U)
                V)
              e (@Sum.inl.{u_1, u_1} U (Prod.{u_1, 0} U Bool) u)))
        (∀ (u : U) (i : Bool),
          Not
            (@Membership.mem.{u_2, u_2} V (Finset.{u_2} V) (@Finset.instMembership.{u_2} V) S
              (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
                (Function.Embedding.{u_1 + 1, u_2 + 1} (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                (RankwidthDomination.ReservoirVertex.{u_1} U) (fun x => V)
                (@Function.instFunLikeEmbedding.{u_1 + 1, u_2 + 1}
                  (RankwidthDomination.ReservoirVertex.{u_1} U) V)
                e (@Sum.inr.{u_1, u_1} U (Prod.{u_1, 0} U Bool) (@Prod.mk.{u_1, 0} U Bool u i)))))) := by
  exact @RankwidthDomination.reservoir_tight_iff

/-- Paper 5.6; component RankwidthDomination.SigmaConstruction.tight_normal_form. -/
theorem RankwidthPaper.result_5_6_1 :
    ∀ {k m b : Nat} (φ : RankwidthDomination.CNF k m) (clique : Bool) (P Q : Finset.{0} (Fin b))
  (R : Fin b → Finset.{0} (Fin b)) (r : Nat),
  (∀ (u : Fin b),
      @Membership.mem.{0, 0} (Fin b) (Finset.{0} (Fin b)) (@Finset.instMembership.{0} (Fin b)) (R u) u) →
    (∀ (u : Fin b), @Eq.{1} Nat (@Finset.card.{0} (Fin b) (R u)) r) →
      @LT.lt.{0} Nat instLTNat (@Finset.card.{0} (Fin b) P) r →
        ∀ (σ ρ : Set.{0} Nat),
          (∀ (n : Nat),
              @LT.lt.{0} Nat instLTNat n r →
                Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ n)) →
            ∀ (S : Finset.{0} (RankwidthDomination.SigmaConstruction.V k m b)),
              @RankwidthDomination.IsSigmaRho.{0} (RankwidthDomination.SigmaConstruction.V k m b)
                  (fun a b_1 =>
                    @instDecidableEqSum.{0, 0} (RankwidthDomination.Vertex k m)
                      (RankwidthDomination.ReservoirVertex.{0} (Fin b))
                      (@RankwidthDomination.instDecidableEqVertex k m)
                      (fun a b_2 =>
                        @instDecidableEqSum.{0, 0} (Fin b) (Prod.{0, 0} (Fin b) Bool) (instDecidableEqFin b)
                          (fun a b_3 =>
                            @instDecidableEqProd.{0, 0} (Fin b) Bool (instDecidableEqFin b)
                              instDecidableEqBool a b_3)
                          a b_2)
                      a b_1)
                  (@RankwidthDomination.SigmaConstruction.graph k m b φ clique P Q R)
                  (@RankwidthDomination.SigmaConstruction.instDecidableRelVAdjGraph k m b φ clique P Q R) σ ρ
                  S →
                @LE.le.{0} Nat instLENat (@Finset.card.{0} (RankwidthDomination.SigmaConstruction.V k m b) S)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        k)) →
                  @Exists.{1}
                    (Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                      RankwidthDomination.Assignment k)
                    fun T =>
                    And
                      (@Eq.{1} (Finset.{0} (RankwidthDomination.SigmaConstruction.V k m b)) S
                        (@RankwidthDomination.SigmaConstruction.selectedAll k m b T))
                      (@Eq.{1} Nat (@Finset.card.{0} (RankwidthDomination.SigmaConstruction.V k m b) S)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            k))) := by
  exact @RankwidthDomination.SigmaConstruction.tight_normal_form

/-- Paper 5.7; component RankwidthDomination.SigmaConstruction.satisfyingEquivSolutions. -/
theorem RankwidthPaper.result_5_7_1 :
    Nonempty.{1}
  ({k m b : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      (clique : Bool) →
        (P Q : Finset.{0} (Fin b)) →
          (R : Fin b → Finset.{0} (Fin b)) →
            (r : Nat) →
              (∀ (u : Fin b),
                  @Membership.mem.{0, 0} (Fin b) (Finset.{0} (Fin b)) (@Finset.instMembership.{0} (Fin b))
                    (R u) u) →
                (∀ (u : Fin b), @Eq.{1} Nat (@Finset.card.{0} (Fin b) (R u)) r) →
                  @LT.lt.{0} Nat instLTNat (@Finset.card.{0} (Fin b) P) r →
                    (σ ρ : Set.{0} Nat) →
                      (∀ (n : Nat),
                          @LT.lt.{0} Nat instLTNat n r →
                            Not
                              (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ n)) →
                        (q : Nat) →
                          @Eq.{1} Nat (@Finset.card.{0} (Fin b) Q) q →
                            Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ q) →
                              (∀ (n : Nat),
                                  @LT.lt.{0} Nat instLTNat q n →
                                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
                                      n) →
                                @ite.{1} Prop (@Eq.{1} Bool clique Bool.true)
                                    (instDecidableEqBool clique Bool.true)
                                    (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) σ
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            k))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) σ
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                                  @ite.{1} Prop (@Eq.{1} Bool clique Bool.true)
                                      (instDecidableEqBool clique Bool.true)
                                      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                                        ρ
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            k)))
                                      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                                        ρ (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Finset.card.{0} (Fin b) P)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                      (∀ (u : Fin b),
                                          @Membership.mem.{0, 0} Nat (Set.{0} Nat)
                                            (@Set.instMembership.{0} Nat) ρ
                                            (@Finset.card.{0} (Fin b) (R u))) →
                                        Equiv.{1, 1} (@RankwidthDomination.SatisfyingAssignments k m φ)
                                          (@RankwidthDomination.SigmaConstruction.BoundedSolutions k m b φ
                                            clique P Q R σ ρ)) := by
  exact ⟨@RankwidthDomination.SigmaConstruction.satisfyingEquivSolutions⟩

/-- Paper 5.7; component RankwidthDomination.SigmaConstruction.cofinite_counts. -/
theorem RankwidthPaper.result_5_7_2 :
    ∀ {k m b : Nat} (φ : RankwidthDomination.CNF k m),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    ∀ (σ ρ : Set.{0} Nat) (t q r : Nat),
      (∀ (n : Nat),
          @LE.le.{0} Nat instLENat t n →
            @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) σ n) →
        Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ q) →
          (∀ (n : Nat),
              @LT.lt.{0} Nat instLTNat q n →
                @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ n) →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r →
              @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ r →
                (∀ (n : Nat),
                    @LT.lt.{0} Nat instLTNat n r →
                      Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ n)) →
                  @LE.le.{0} Nat instLENat t b →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        b →
                      ∀ (P Q : Finset.{0} (Fin b)) (R : Fin b → Finset.{0} (Fin b)),
                        @Eq.{1} Nat (@Finset.card.{0} (Fin b) P)
                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) r
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          @Eq.{1} Nat (@Finset.card.{0} (Fin b) Q) q →
                            (∀ (u : Fin b),
                                @Membership.mem.{0, 0} (Fin b) (Finset.{0} (Fin b))
                                  (@Finset.instMembership.{0} (Fin b)) (R u) u) →
                              (∀ (u : Fin b), @Eq.{1} Nat (@Finset.card.{0} (Fin b) (R u)) r) →
                                And
                                  (@Eq.{1} Nat
                                    (Nat.card.{0}
                                      (@RankwidthDomination.SigmaConstruction.BoundedSolutions k m b φ
                                        Bool.true P Q R σ ρ))
                                    (Nat.card.{0}
                                      (@RankwidthDomination.SigmaConstruction.ExactSolutions k m b φ Bool.true
                                        P Q R σ ρ)))
                                  (@Eq.{1} Nat
                                    (Nat.card.{0}
                                      (@RankwidthDomination.SigmaConstruction.ExactSolutions k m b φ Bool.true
                                        P Q R σ ρ))
                                    (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ))) := by
  exact @RankwidthDomination.SigmaConstruction.cofinite_counts

/-- Paper 5.7; component RankwidthDomination.SigmaConstruction.cofinite_branch_exists. -/
theorem RankwidthPaper.result_5_7_3 :
    ∀ (σ ρ : Set.{0} Nat),
  @Set.Finite.{0} Nat (@HasCompl.compl.{0} (Set.{0} Nat) (@Set.instHasCompl.{0} Nat) σ) →
    @Set.Finite.{0} Nat (@HasCompl.compl.{0} (Set.{0} Nat) (@Set.instHasCompl.{0} Nat) ρ) →
      Not
          (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
        @Exists.{1} Nat fun b =>
          @Exists.{1} (Finset.{0} (Fin b)) fun P =>
            @Exists.{1} (Finset.{0} (Fin b)) fun Q =>
              @Exists.{1} (Fin b → Finset.{0} (Fin b)) fun R =>
                ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
                    And
                      (@Eq.{1} Nat
                        (Nat.card.{0}
                          (@RankwidthDomination.SigmaConstruction.BoundedSolutions k m b φ Bool.true P Q R σ
                            ρ))
                        (Nat.card.{0}
                          (@RankwidthDomination.SigmaConstruction.ExactSolutions k m b φ Bool.true P Q R σ
                            ρ)))
                      (@Eq.{1} Nat
                        (Nat.card.{0}
                          (@RankwidthDomination.SigmaConstruction.ExactSolutions k m b φ Bool.true P Q R σ ρ))
                        (Nat.card.{0} (@RankwidthDomination.SatisfyingAssignments k m φ))) := by
  exact @RankwidthDomination.SigmaConstruction.cofinite_branch_exists

/-- Paper 5.8; component RankwidthDomination.SigmaWidth.clique_prefix_bound. -/
theorem RankwidthPaper.result_5_8_1 :
    ∀ {k m b : Nat} (φ : RankwidthDomination.CNF k m) (P Q : Finset.{0} (Fin b)) (R : Fin b → Finset.{0} (Fin b))
  (n : Nat),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.cutRank.{0} (RankwidthDomination.SigmaConstruction.V k m b)
      (@instFintypeSum.{0, 0} (RankwidthDomination.Vertex k m)
        (RankwidthDomination.ReservoirVertex.{0} (Fin b)) (@RankwidthDomination.instFintypeVertex k m)
        (@instFintypeSum.{0, 0} (Fin b) (Prod.{0, 0} (Fin b) Bool) (Fin.fintype b)
          (@instFintypeProd.{0, 0} (Fin b) Bool (Fin.fintype b) Bool.fintype)))
      (@RankwidthDomination.SigmaConstruction.graph k m b φ Bool.true P Q R)
      (@RankwidthDomination.SigmaWidth.listPrefix.{0} (RankwidthDomination.SigmaConstruction.V k m b)
        (RankwidthDomination.SigmaWidth.vertices k m b) n))
    (@Max.max.{0} Nat Nat.instMax
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))) := by
  exact @RankwidthDomination.SigmaWidth.clique_prefix_bound

/-- Paper A.1; component RankwidthDomination.exactStandardEqualityTest. -/
theorem RankwidthPaper.result_A_1_1 :
    ∀ {k : Nat} (X Y : RankwidthDomination.Assignment k),
  Iff
    (∀ (j : Fin k) (p r : RankwidthDomination.Row k),
      @Ne.{1} (RankwidthDomination.Row k) r
          (@OfNat.ofNat.{0} (RankwidthDomination.Row k) (nat_lit 0)
            (@Zero.toOfNat0.{0} (RankwidthDomination.Row k)
              (@Pi.instZero.{0, 0} (Fin k) (fun a => RankwidthDomination.Bit) fun i =>
                @MulZeroClass.toZero.{0} RankwidthDomination.Bit
                  (@NonUnitalNonAssocSemiring.toMulZeroClass.{0} RankwidthDomination.Bit
                    (@NonUnitalNonAssocCommSemiring.toNonUnitalNonAssocSemiring.{0} RankwidthDomination.Bit
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocCommSemiring.{0} RankwidthDomination.Bit
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} RankwidthDomination.Bit
                          (@CommRing.toNonUnitalCommRing.{0} RankwidthDomination.Bit
                            (ZMod.commRing
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))) →
        @RankwidthDomination.standardCheckerHasNeighbor k X Y j p r)
    (@Eq.{1} (RankwidthDomination.Assignment k) X Y) := by
  exact @RankwidthDomination.exactStandardEqualityTest

/-- Paper A.1; component RankwidthDomination.CheckerRank.standardLeftIncidence_submatrix_rank_le. -/
theorem RankwidthPaper.result_A_1_2.{u_1, u_2} :
    ∀ {k : Nat} {I : Type u_1} {J : Type u_2} [inst : Fintype.{u_2} J]
  (rows : I → RankwidthDomination.CheckerRank.AssignmentVertex k)
  (cols : J → RankwidthDomination.CheckerRank.StandardChecker k),
  @LE.le.{0} Nat instLENat
    (@Matrix.rank.{u_1, u_2, 0} I J RankwidthDomination.CheckerRank.Bit inst
      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Matrix.submatrix.{0, u_1, 0, 0, u_2} I (RankwidthDomination.CheckerRank.AssignmentVertex k)
        (RankwidthDomination.CheckerRank.StandardChecker k) J RankwidthDomination.CheckerRank.Bit
        (RankwidthDomination.CheckerRank.standardLeftIncidence k) rows cols))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) := by
  exact @RankwidthDomination.CheckerRank.standardLeftIncidence_submatrix_rank_le

/-- Paper A.1; component RankwidthDomination.CheckerRank.standardRightIncidence_submatrix_rank_le. -/
theorem RankwidthPaper.result_A_1_3.{u_1, u_2} :
    ∀ {k : Nat} {I : Type u_1} {J : Type u_2} [inst : Fintype.{u_2} J]
  (rows : I → RankwidthDomination.CheckerRank.AssignmentVertex k)
  (cols : J → RankwidthDomination.CheckerRank.StandardChecker k),
  @LE.le.{0} Nat instLENat
    (@Matrix.rank.{u_1, u_2, 0} I J RankwidthDomination.CheckerRank.Bit inst
      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Matrix.submatrix.{0, u_1, 0, 0, u_2} I (RankwidthDomination.CheckerRank.AssignmentVertex k)
        (RankwidthDomination.CheckerRank.StandardChecker k) J RankwidthDomination.CheckerRank.Bit
        (RankwidthDomination.CheckerRank.standardRightIncidence k) rows cols))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) := by
  exact @RankwidthDomination.CheckerRank.standardRightIncidence_submatrix_rank_le

/-- Paper A.1; component RankwidthDomination.Standard.vertex_card. -/
theorem RankwidthPaper.result_A_1_4 :
    ∀ (k m : Nat),
  @Eq.{1} Nat
    (@Fintype.card.{0} (RankwidthDomination.Standard.Vertex k m)
      (@RankwidthDomination.Standard.instFintypeVertex k m))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m k)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  exact @RankwidthDomination.Standard.vertex_card

/-- Paper A.1; component RankwidthDomination.Standard.satisfyingEquivDominating. -/
theorem RankwidthPaper.result_A_1_5 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      (s : Bool) →
        Equiv.{1, 1} (@RankwidthDomination.Standard.SatisfyingAssignments k m φ)
          (@RankwidthDomination.Standard.BoundedDominatingSets k m φ s)) := by
  exact ⟨@RankwidthDomination.Standard.satisfyingEquivDominating⟩

/-- Paper A.1; component RankwidthDomination.Standard.satisfyingEquivBipDominating. -/
theorem RankwidthPaper.result_A_1_6 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      Equiv.{1, 1} (@RankwidthDomination.Standard.SatisfyingAssignments k m φ)
        (@RankwidthDomination.Standard.BipBoundedDominatingSets k m φ)) := by
  exact ⟨@RankwidthDomination.Standard.satisfyingEquivBipDominating⟩

/-- Paper A.1; component RankwidthDomination.Standard.satisfyingEquivIndependent. -/
theorem RankwidthPaper.result_A_1_7 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      Equiv.{1, 1} (@RankwidthDomination.Standard.SatisfyingAssignments k m φ)
        (@RankwidthDomination.Standard.BoundedVariantSets.{0} (RankwidthDomination.Standard.Vertex k m)
          (@RankwidthDomination.Standard.instDecidableEqVertex k m)
          (@RankwidthDomination.Standard.coreGraph k m φ Bool.false)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            k)
          fun D =>
          @SimpleGraph.IsIndepSet.{0} (RankwidthDomination.Standard.Vertex k m)
            (@RankwidthDomination.Standard.coreGraph k m φ Bool.false)
            (@Finset.toSet.{0} (RankwidthDomination.Standard.Vertex k m) D))) := by
  exact ⟨@RankwidthDomination.Standard.satisfyingEquivIndependent⟩

/-- Paper A.1; component RankwidthDomination.Standard.satisfyingEquivSplitConnected. -/
theorem RankwidthPaper.result_A_1_8 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
        Equiv.{1, 1} (@RankwidthDomination.Standard.SatisfyingAssignments k m φ)
          (@RankwidthDomination.Standard.BoundedVariantSets.{0} (RankwidthDomination.Standard.Vertex k m)
            (@RankwidthDomination.Standard.instDecidableEqVertex k m)
            (@RankwidthDomination.Standard.coreGraph k m φ Bool.true)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@RankwidthDomination.Standard.ConnectedSelected.{0} (RankwidthDomination.Standard.Vertex k m)
              (@RankwidthDomination.Standard.coreGraph k m φ Bool.true)))) := by
  exact ⟨@RankwidthDomination.Standard.satisfyingEquivSplitConnected⟩

/-- Paper A.1; component RankwidthDomination.Standard.satisfyingEquivSplitTotal. -/
theorem RankwidthPaper.result_A_1_9 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            k) →
        Equiv.{1, 1} (@RankwidthDomination.Standard.SatisfyingAssignments k m φ)
          (@RankwidthDomination.Standard.BoundedVariantSets.{0} (RankwidthDomination.Standard.Vertex k m)
            (@RankwidthDomination.Standard.instDecidableEqVertex k m)
            (@RankwidthDomination.Standard.coreGraph k m φ Bool.true)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@RankwidthDomination.Standard.TotalDominates.{0} (RankwidthDomination.Standard.Vertex k m)
              (@RankwidthDomination.Standard.instDecidableEqVertex k m)
              (@RankwidthDomination.Standard.coreGraph k m φ Bool.true)))) := by
  exact ⟨@RankwidthDomination.Standard.satisfyingEquivSplitTotal⟩

/-- Paper A.1; component RankwidthDomination.Standard.satisfyingEquivBipConnected. -/
theorem RankwidthPaper.result_A_1_10 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      Equiv.{1, 1} (@RankwidthDomination.Standard.SatisfyingAssignments k m φ)
        (@RankwidthDomination.Standard.BoundedVariantSets.{0} (RankwidthDomination.Standard.BipVertex k m)
          (@RankwidthDomination.Standard.instDecidableEqBipVertex k m)
          (@RankwidthDomination.Standard.bipGraph k m φ)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@RankwidthDomination.Standard.ConnectedSelected.{0} (RankwidthDomination.Standard.BipVertex k m)
            (@RankwidthDomination.Standard.bipGraph k m φ)))) := by
  exact ⟨@RankwidthDomination.Standard.satisfyingEquivBipConnected⟩

/-- Paper A.1; component RankwidthDomination.Standard.satisfyingEquivBipTotal. -/
theorem RankwidthPaper.result_A_1_11 :
    Nonempty.{1}
  ({k m : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
        Equiv.{1, 1} (@RankwidthDomination.Standard.SatisfyingAssignments k m φ)
          (@RankwidthDomination.Standard.BoundedVariantSets.{0} (RankwidthDomination.Standard.BipVertex k m)
            (@RankwidthDomination.Standard.instDecidableEqBipVertex k m)
            (@RankwidthDomination.Standard.bipGraph k m φ)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                k)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@RankwidthDomination.Standard.TotalDominates.{0} (RankwidthDomination.Standard.BipVertex k m)
              (@RankwidthDomination.Standard.instDecidableEqBipVertex k m)
              (@RankwidthDomination.Standard.bipGraph k m φ)))) := by
  exact ⟨@RankwidthDomination.Standard.satisfyingEquivBipTotal⟩

/-- Paper A.1; component RankwidthDomination.Standard.SigmaConstruction.satisfyingEquivSolutions. -/
theorem RankwidthPaper.result_A_1_12 :
    Nonempty.{1}
  ({k m b : Nat} →
    (φ : RankwidthDomination.CNF k m) →
      (clique : Bool) →
        (P Q : Finset.{0} (Fin b)) →
          (R : Fin b → Finset.{0} (Fin b)) →
            (r : Nat) →
              (∀ (u : Fin b),
                  @Membership.mem.{0, 0} (Fin b) (Finset.{0} (Fin b)) (@Finset.instMembership.{0} (Fin b))
                    (R u) u) →
                (∀ (u : Fin b), @Eq.{1} Nat (@Finset.card.{0} (Fin b) (R u)) r) →
                  @LT.lt.{0} Nat instLTNat (@Finset.card.{0} (Fin b) P) r →
                    (σ ρ : Set.{0} Nat) →
                      (∀ (n : Nat),
                          @LT.lt.{0} Nat instLTNat n r →
                            Not
                              (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ n)) →
                        (q : Nat) →
                          @Eq.{1} Nat (@Finset.card.{0} (Fin b) Q) q →
                            Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ q) →
                              (∀ (n : Nat),
                                  @LT.lt.{0} Nat instLTNat q n →
                                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
                                      n) →
                                @ite.{1} Prop (@Eq.{1} Bool clique Bool.true)
                                    (instDecidableEqBool clique Bool.true)
                                    (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) σ
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            k))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) σ
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                                  @ite.{1} Prop (@Eq.{1} Bool clique Bool.true)
                                      (instDecidableEqBool clique Bool.true)
                                      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                                        ρ
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            k)))
                                      (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat)
                                        ρ (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                    @Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) ρ
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Finset.card.{0} (Fin b) P)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                      (∀ (u : Fin b),
                                          @Membership.mem.{0, 0} Nat (Set.{0} Nat)
                                            (@Set.instMembership.{0} Nat) ρ
                                            (@Finset.card.{0} (Fin b) (R u))) →
                                        Equiv.{1, 1}
                                          (@RankwidthDomination.Standard.SatisfyingAssignments k m φ)
                                          (@RankwidthDomination.Standard.SigmaConstruction.BoundedSolutions k
                                            m b φ clique P Q R σ ρ)) := by
  exact ⟨@RankwidthDomination.Standard.SigmaConstruction.satisfyingEquivSolutions⟩

/-- Paper A.1; component RankwidthDomination.Standard.basic_prefix_bound. -/
theorem RankwidthPaper.result_A_1_13 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (n : Nat),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.cutRank.{0} (RankwidthDomination.Standard.Vertex k m)
      (@RankwidthDomination.Standard.instFintypeVertex k m)
      (@RankwidthDomination.Standard.coreGraph k m φ Bool.false)
      (@setOf.{0} (RankwidthDomination.Standard.Vertex k m) fun v =>
        @Membership.mem.{0, 0} (RankwidthDomination.Standard.Vertex k m)
          (List.{0} (RankwidthDomination.Standard.Vertex k m))
          (@List.instMembership.{0} (RankwidthDomination.Standard.Vertex k m))
          (@List.take.{0} (RankwidthDomination.Standard.Vertex k m) n
            (RankwidthDomination.Standard.vertices k m))
          v))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := by
  exact @RankwidthDomination.Standard.basic_prefix_bound

/-- Paper A.1; component RankwidthDomination.Standard.split_prefix_bound. -/
theorem RankwidthPaper.result_A_1_14 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (n : Nat),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.cutRank.{0} (RankwidthDomination.Standard.Vertex k m)
      (@RankwidthDomination.Standard.instFintypeVertex k m)
      (@RankwidthDomination.Standard.coreGraph k m φ Bool.true)
      (@setOf.{0} (RankwidthDomination.Standard.Vertex k m) fun v =>
        @Membership.mem.{0, 0} (RankwidthDomination.Standard.Vertex k m)
          (List.{0} (RankwidthDomination.Standard.Vertex k m))
          (@List.instMembership.{0} (RankwidthDomination.Standard.Vertex k m))
          (@List.take.{0} (RankwidthDomination.Standard.Vertex k m) n
            (RankwidthDomination.Standard.vertices k m))
          v))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) := by
  exact @RankwidthDomination.Standard.split_prefix_bound

/-- Paper A.1; component RankwidthDomination.Standard.bip_prefix_bound. -/
theorem RankwidthPaper.result_A_1_15 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (n : Nat),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.cutRank.{0} (RankwidthDomination.Standard.BipVertex k m)
      (@RankwidthDomination.Standard.instFintypeBipVertex k m) (@RankwidthDomination.Standard.bipGraph k m φ)
      (@setOf.{0} (RankwidthDomination.Standard.BipVertex k m) fun v =>
        @Membership.mem.{0, 0} (RankwidthDomination.Standard.BipVertex k m)
          (List.{0} (RankwidthDomination.Standard.BipVertex k m))
          (@List.instMembership.{0} (RankwidthDomination.Standard.BipVertex k m))
          (@List.take.{0} (RankwidthDomination.Standard.BipVertex k m) n
            (RankwidthDomination.Standard.bipVertices k m))
          v))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) := by
  exact @RankwidthDomination.Standard.bip_prefix_bound

/-- Paper A.1; component RankwidthDomination.Standard.SigmaConstruction.independent_prefix_bound. -/
theorem RankwidthPaper.result_A_1_16 :
    ∀ {k m b : Nat} (φ : RankwidthDomination.CNF k m) (Q : Finset.{0} (Fin b)) (R : Fin b → Finset.{0} (Fin b))
  (n : Nat),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.cutRank.{0} (RankwidthDomination.Standard.SigmaConstruction.V k m b)
      (@instFintypeSum.{0, 0} (RankwidthDomination.Standard.Vertex k m)
        (RankwidthDomination.ReservoirVertex.{0} (Fin b))
        (@RankwidthDomination.Standard.instFintypeVertex k m)
        (@instFintypeSum.{0, 0} (Fin b) (Prod.{0, 0} (Fin b) Bool) (Fin.fintype b)
          (@instFintypeProd.{0, 0} (Fin b) Bool (Fin.fintype b) Bool.fintype)))
      (@RankwidthDomination.Standard.SigmaConstruction.graph k m b φ Bool.false
        (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin b)) (@Finset.instEmptyCollection.{0} (Fin b)))
        Q R)
      (@setOf.{0} (RankwidthDomination.Standard.SigmaConstruction.V k m b) fun v =>
        @Membership.mem.{0, 0} (RankwidthDomination.Standard.SigmaConstruction.V k m b)
          (List.{0} (RankwidthDomination.Standard.SigmaConstruction.V k m b))
          (@List.instMembership.{0} (RankwidthDomination.Standard.SigmaConstruction.V k m b))
          (@List.take.{0} (RankwidthDomination.Standard.SigmaConstruction.V k m b) n
            (RankwidthDomination.Standard.SigmaConstruction.vertices k m b))
          v))
    (@Max.max.{0} Nat Nat.instMax
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) := by
  exact @RankwidthDomination.Standard.SigmaConstruction.independent_prefix_bound

/-- Paper A.1; component RankwidthDomination.Standard.SigmaConstruction.clique_prefix_bound. -/
theorem RankwidthPaper.result_A_1_17 :
    ∀ {k m b : Nat} (φ : RankwidthDomination.CNF k m) (P Q : Finset.{0} (Fin b)) (R : Fin b → Finset.{0} (Fin b))
  (n : Nat),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.cutRank.{0} (RankwidthDomination.Standard.SigmaConstruction.V k m b)
      (@instFintypeSum.{0, 0} (RankwidthDomination.Standard.Vertex k m)
        (RankwidthDomination.ReservoirVertex.{0} (Fin b))
        (@RankwidthDomination.Standard.instFintypeVertex k m)
        (@instFintypeSum.{0, 0} (Fin b) (Prod.{0, 0} (Fin b) Bool) (Fin.fintype b)
          (@instFintypeProd.{0, 0} (Fin b) Bool (Fin.fintype b) Bool.fintype)))
      (@RankwidthDomination.Standard.SigmaConstruction.graph k m b φ Bool.true P Q R)
      (@setOf.{0} (RankwidthDomination.Standard.SigmaConstruction.V k m b) fun v =>
        @Membership.mem.{0, 0} (RankwidthDomination.Standard.SigmaConstruction.V k m b)
          (List.{0} (RankwidthDomination.Standard.SigmaConstruction.V k m b))
          (@List.instMembership.{0} (RankwidthDomination.Standard.SigmaConstruction.V k m b))
          (@List.take.{0} (RankwidthDomination.Standard.SigmaConstruction.V k m b) n
            (RankwidthDomination.Standard.SigmaConstruction.vertices k m b))
          v))
    (@Max.max.{0} Nat Nat.instMax
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k)
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))) := by
  exact @RankwidthDomination.Standard.SigmaConstruction.clique_prefix_bound

/-- Paper B.1; component RankwidthDomination.B1RAM.basic_construction_general. -/
theorem RankwidthPaper.result_B_1_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    And
      (@Eq.{1} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
        (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
          (List.{0} Nat)
          (@Prod.fst.{0, 0}
            (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
              (List.{0} Nat))
            Nat (RankwidthDomination.B1RAM.output k m)))
        (RankwidthDomination.StandardAlgorithm.build k m))
      (And
        (@Eq.{1} (List.{0} Nat)
          (@Prod.snd.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
            (List.{0} Nat)
            (@Prod.fst.{0, 0}
              (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                (List.{0} Nat))
              Nat (RankwidthDomination.B1RAM.output k m)))
          (@List.cons.{0} Nat k
            (@List.cons.{0} Nat m
              (@RankwidthDomination.B1RAM.treeCode (RankwidthDomination.Standard.Vertex k m)
                (@RankwidthDomination.B1RAM.vertexCode k m)
                (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                  (List.{0} Nat)
                  (@Prod.fst.{0, 0}
                    (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                      (List.{0} Nat))
                    Nat (RankwidthDomination.B1RAM.output k m)))))))
        (And
          (@List.Nodup.{0} (RankwidthDomination.Standard.Vertex k m)
            (@RankwidthDomination.RankTree.leaves.{0} (RankwidthDomination.Standard.Vertex k m)
              (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                (List.{0} Nat)
                (@Prod.fst.{0, 0}
                  (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                    (List.{0} Nat))
                  Nat (RankwidthDomination.B1RAM.output k m)))))
          (And
            (@Eq.{1} (Set.{0} (RankwidthDomination.Standard.Vertex k m))
              (@RankwidthDomination.RankTree.leafSet.{0} (RankwidthDomination.Standard.Vertex k m)
                (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                  (List.{0} Nat)
                  (@Prod.fst.{0, 0}
                    (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                      (List.{0} Nat))
                    Nat (RankwidthDomination.B1RAM.output k m))))
              (@Set.univ.{0} (RankwidthDomination.Standard.Vertex k m)))
            (And
              (@LE.le.{0} Nat instLENat
                (@RankwidthDomination.RankTree.width.{0} (RankwidthDomination.Standard.Vertex k m)
                  (@RankwidthDomination.Standard.instFintypeVertex k m)
                  (@RankwidthDomination.Standard.coreGraph k m φ Bool.false)
                  (@Prod.fst.{0, 0}
                    (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                    (List.{0} Nat)
                    (@Prod.fst.{0, 0}
                      (Prod.{0, 0}
                        (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                        (List.{0} Nat))
                      Nat (RankwidthDomination.B1RAM.output k m))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@LE.le.{0} Nat instLENat
                (@Prod.snd.{0, 0}
                  (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                    (List.{0} Nat))
                  Nat (RankwidthDomination.B1RAM.output k m))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2000) (instOfNatNat (nat_lit 2000)))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Fintype.card.{0} (RankwidthDomination.Standard.Vertex k m)
                        (@RankwidthDomination.Standard.instFintypeVertex k m))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))) := by
  exact @RankwidthDomination.B1RAM.basic_construction_general

/-- Paper B.1; component RankwidthDomination.B1RAM.basic_construction. -/
theorem RankwidthPaper.result_B_1_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
    And
      (@Eq.{1} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
        (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
          (List.{0} Nat)
          (@Prod.fst.{0, 0}
            (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
              (List.{0} Nat))
            Nat (RankwidthDomination.B1RAM.output k m)))
        (RankwidthDomination.StandardAlgorithm.build k m))
      (And
        (@Eq.{1} (List.{0} Nat)
          (@Prod.snd.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
            (List.{0} Nat)
            (@Prod.fst.{0, 0}
              (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                (List.{0} Nat))
              Nat (RankwidthDomination.B1RAM.output k m)))
          (@List.cons.{0} Nat k
            (@List.cons.{0} Nat m
              (@RankwidthDomination.B1RAM.treeCode (RankwidthDomination.Standard.Vertex k m)
                (@RankwidthDomination.B1RAM.vertexCode k m)
                (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                  (List.{0} Nat)
                  (@Prod.fst.{0, 0}
                    (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                      (List.{0} Nat))
                    Nat (RankwidthDomination.B1RAM.output k m)))))))
        (And
          (@List.Nodup.{0} (RankwidthDomination.Standard.Vertex k m)
            (@RankwidthDomination.RankTree.leaves.{0} (RankwidthDomination.Standard.Vertex k m)
              (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                (List.{0} Nat)
                (@Prod.fst.{0, 0}
                  (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                    (List.{0} Nat))
                  Nat (RankwidthDomination.B1RAM.output k m)))))
          (And
            (@Eq.{1} (Set.{0} (RankwidthDomination.Standard.Vertex k m))
              (@RankwidthDomination.RankTree.leafSet.{0} (RankwidthDomination.Standard.Vertex k m)
                (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                  (List.{0} Nat)
                  (@Prod.fst.{0, 0}
                    (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                      (List.{0} Nat))
                    Nat (RankwidthDomination.B1RAM.output k m))))
              (@Set.univ.{0} (RankwidthDomination.Standard.Vertex k m)))
            (And
              (@LE.le.{0} Nat instLENat
                (@RankwidthDomination.RankTree.width.{0} (RankwidthDomination.Standard.Vertex k m)
                  (@RankwidthDomination.Standard.instFintypeVertex k m)
                  (@RankwidthDomination.Standard.coreGraph k m φ Bool.false)
                  (@Prod.fst.{0, 0}
                    (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                    (List.{0} Nat)
                    (@Prod.fst.{0, 0}
                      (Prod.{0, 0}
                        (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                        (List.{0} Nat))
                      Nat (RankwidthDomination.B1RAM.output k m))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k))
              (@LE.le.{0} Nat instLENat
                (@Prod.snd.{0, 0}
                  (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                    (List.{0} Nat))
                  Nat (RankwidthDomination.B1RAM.output k m))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2000) (instOfNatNat (nat_lit 2000)))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Fintype.card.{0} (RankwidthDomination.Standard.Vertex k m)
                        (@RankwidthDomination.Standard.instFintypeVertex k m))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))) := by
  exact @RankwidthDomination.B1RAM.basic_construction

/-- Paper B.1; component RankwidthDomination.B1RAM.split_construction. -/
theorem RankwidthPaper.result_B_1_3 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    And
      (@Eq.{1} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
        (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
          (List.{0} Nat)
          (@Prod.fst.{0, 0}
            (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
              (List.{0} Nat))
            Nat (RankwidthDomination.B1RAM.output k m)))
        (RankwidthDomination.StandardAlgorithm.build k m))
      (And
        (@Eq.{1} (List.{0} Nat)
          (@Prod.snd.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
            (List.{0} Nat)
            (@Prod.fst.{0, 0}
              (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                (List.{0} Nat))
              Nat (RankwidthDomination.B1RAM.output k m)))
          (@List.cons.{0} Nat k
            (@List.cons.{0} Nat m
              (@RankwidthDomination.B1RAM.treeCode (RankwidthDomination.Standard.Vertex k m)
                (@RankwidthDomination.B1RAM.vertexCode k m)
                (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                  (List.{0} Nat)
                  (@Prod.fst.{0, 0}
                    (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                      (List.{0} Nat))
                    Nat (RankwidthDomination.B1RAM.output k m)))))))
        (And
          (@List.Nodup.{0} (RankwidthDomination.Standard.Vertex k m)
            (@RankwidthDomination.RankTree.leaves.{0} (RankwidthDomination.Standard.Vertex k m)
              (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                (List.{0} Nat)
                (@Prod.fst.{0, 0}
                  (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                    (List.{0} Nat))
                  Nat (RankwidthDomination.B1RAM.output k m)))))
          (And
            (@Eq.{1} (Set.{0} (RankwidthDomination.Standard.Vertex k m))
              (@RankwidthDomination.RankTree.leafSet.{0} (RankwidthDomination.Standard.Vertex k m)
                (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                  (List.{0} Nat)
                  (@Prod.fst.{0, 0}
                    (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                      (List.{0} Nat))
                    Nat (RankwidthDomination.B1RAM.output k m))))
              (@Set.univ.{0} (RankwidthDomination.Standard.Vertex k m)))
            (And
              (@LE.le.{0} Nat instLENat
                (@RankwidthDomination.RankTree.width.{0} (RankwidthDomination.Standard.Vertex k m)
                  (@RankwidthDomination.Standard.instFintypeVertex k m)
                  (@RankwidthDomination.Standard.coreGraph k m φ Bool.true)
                  (@Prod.fst.{0, 0}
                    (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                    (List.{0} Nat)
                    (@Prod.fst.{0, 0}
                      (Prod.{0, 0}
                        (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                        (List.{0} Nat))
                      Nat (RankwidthDomination.B1RAM.output k m))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@LE.le.{0} Nat instLENat
                (@Prod.snd.{0, 0}
                  (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
                    (List.{0} Nat))
                  Nat (RankwidthDomination.B1RAM.output k m))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2000) (instOfNatNat (nat_lit 2000)))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Fintype.card.{0} (RankwidthDomination.Standard.Vertex k m)
                        (@RankwidthDomination.Standard.instFintypeVertex k m))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))) := by
  exact @RankwidthDomination.B1RAM.split_construction

/-- Paper B.1; component RankwidthDomination.B1RAM.bip_construction. -/
theorem RankwidthPaper.result_B_1_4 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    And
      (@Eq.{1} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
        (@Prod.fst.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
          (List.{0} Nat)
          (@Prod.fst.{0, 0}
            (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
              (List.{0} Nat))
            Nat (RankwidthDomination.B1RAM.bipOutput k m)))
        (RankwidthDomination.StandardAlgorithm.bipBuild k m))
      (And
        (@Eq.{1} (List.{0} Nat)
          (@Prod.snd.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
            (List.{0} Nat)
            (@Prod.fst.{0, 0}
              (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
                (List.{0} Nat))
              Nat (RankwidthDomination.B1RAM.bipOutput k m)))
          (@List.cons.{0} Nat k
            (@List.cons.{0} Nat m
              (@RankwidthDomination.B1RAM.treeCode (RankwidthDomination.Standard.BipVertex k m)
                (@RankwidthDomination.B1RAM.bipVertexCode k m)
                (@Prod.fst.{0, 0}
                  (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
                  (List.{0} Nat)
                  (@Prod.fst.{0, 0}
                    (Prod.{0, 0}
                      (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
                      (List.{0} Nat))
                    Nat (RankwidthDomination.B1RAM.bipOutput k m)))))))
        (And
          (@List.Nodup.{0} (RankwidthDomination.Standard.BipVertex k m)
            (@RankwidthDomination.RankTree.leaves.{0} (RankwidthDomination.Standard.BipVertex k m)
              (@Prod.fst.{0, 0}
                (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m)) (List.{0} Nat)
                (@Prod.fst.{0, 0}
                  (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
                    (List.{0} Nat))
                  Nat (RankwidthDomination.B1RAM.bipOutput k m)))))
          (And
            (@Eq.{1} (Set.{0} (RankwidthDomination.Standard.BipVertex k m))
              (@RankwidthDomination.RankTree.leafSet.{0} (RankwidthDomination.Standard.BipVertex k m)
                (@Prod.fst.{0, 0}
                  (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
                  (List.{0} Nat)
                  (@Prod.fst.{0, 0}
                    (Prod.{0, 0}
                      (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
                      (List.{0} Nat))
                    Nat (RankwidthDomination.B1RAM.bipOutput k m))))
              (@Set.univ.{0} (RankwidthDomination.Standard.BipVertex k m)))
            (And
              (@LE.le.{0} Nat instLENat
                (@RankwidthDomination.RankTree.width.{0} (RankwidthDomination.Standard.BipVertex k m)
                  (@RankwidthDomination.Standard.instFintypeBipVertex k m)
                  (@RankwidthDomination.Standard.bipGraph k m φ)
                  (@Prod.fst.{0, 0}
                    (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
                    (List.{0} Nat)
                    (@Prod.fst.{0, 0}
                      (Prod.{0, 0}
                        (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
                        (List.{0} Nat))
                      Nat (RankwidthDomination.B1RAM.bipOutput k m))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@LE.le.{0} Nat instLENat
                (@Prod.snd.{0, 0}
                  (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
                    (List.{0} Nat))
                  Nat (RankwidthDomination.B1RAM.bipOutput k m))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2000) (instOfNatNat (nat_lit 2000)))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@Fintype.card.{0} (RankwidthDomination.Standard.BipVertex k m)
                        (@RankwidthDomination.Standard.instFintypeBipVertex k m))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))) := by
  exact @RankwidthDomination.B1RAM.bip_construction

/-- Paper B.1; component RankwidthDomination.B1RAM.output_value. -/
theorem RankwidthPaper.result_B_1_5 :
    ∀ (k m : Nat),
  @Eq.{1}
    (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m)) (List.{0} Nat))
    (@Prod.fst.{0, 0}
      (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
        (List.{0} Nat))
      Nat (RankwidthDomination.B1RAM.output k m))
    (@Prod.mk.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
      (List.{0} Nat) (RankwidthDomination.StandardAlgorithm.build k m)
      (@List.cons.{0} Nat k
        (@List.cons.{0} Nat m
          (@RankwidthDomination.B1RAM.treeCode (RankwidthDomination.Standard.Vertex k m)
            (@RankwidthDomination.B1RAM.vertexCode k m) (RankwidthDomination.StandardAlgorithm.build k m))))) := by
  exact @RankwidthDomination.B1RAM.output_value

/-- Paper B.1; component RankwidthDomination.B1RAM.bipOutput_value. -/
theorem RankwidthPaper.result_B_1_6 :
    ∀ (k m : Nat),
  @Eq.{1}
    (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
      (List.{0} Nat))
    (@Prod.fst.{0, 0}
      (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
        (List.{0} Nat))
      Nat (RankwidthDomination.B1RAM.bipOutput k m))
    (@Prod.mk.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
      (List.{0} Nat) (RankwidthDomination.StandardAlgorithm.bipBuild k m)
      (@List.cons.{0} Nat k
        (@List.cons.{0} Nat m
          (@RankwidthDomination.B1RAM.treeCode (RankwidthDomination.Standard.BipVertex k m)
            (@RankwidthDomination.B1RAM.bipVertexCode k m)
            (RankwidthDomination.StandardAlgorithm.bipBuild k m))))) := by
  exact @RankwidthDomination.B1RAM.bipOutput_value

/-- Paper B.1; component RankwidthDomination.B1RAM.output_steps. -/
theorem RankwidthPaper.result_B_1_7 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    @LE.le.{0} Nat instLENat
      (@Prod.snd.{0, 0}
        (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.Vertex k m))
          (List.{0} Nat))
        Nat (RankwidthDomination.B1RAM.output k m))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2000) (instOfNatNat (nat_lit 2000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Fintype.card.{0} (RankwidthDomination.Standard.Vertex k m)
              (@RankwidthDomination.Standard.instFintypeVertex k m))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))) := by
  exact @RankwidthDomination.B1RAM.output_steps

/-- Paper B.1; component RankwidthDomination.B1RAM.bipOutput_steps. -/
theorem RankwidthPaper.result_B_1_8 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    @LE.le.{0} Nat instLENat
      (@Prod.snd.{0, 0}
        (Prod.{0, 0} (RankwidthDomination.RankTree.{0} (RankwidthDomination.Standard.BipVertex k m))
          (List.{0} Nat))
        Nat (RankwidthDomination.B1RAM.bipOutput k m))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2000) (instOfNatNat (nat_lit 2000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@Fintype.card.{0} (RankwidthDomination.Standard.BipVertex k m)
              (@RankwidthDomination.Standard.instFintypeBipVertex k m))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))) := by
  exact @RankwidthDomination.B1RAM.bipOutput_steps

/-- Paper B.1; component RankwidthDomination.RankDecomposition.toGraphDecomposition_width_le. -/
theorem RankwidthPaper.result_B_1_9.{u_1} :
    ∀ {V : Type u_1} [inst : Fintype.{u_1} V] (d : RankwidthDomination.RankDecomposition.{u_1} V)
  (hsize :
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@List.length.{u_1} V
        (@RankwidthDomination.RankTree.leaves.{u_1} V
          (@RankwidthDomination.RankDecomposition.tree.{u_1} V d))))
  (G : SimpleGraph.{u_1} V),
  @LE.le.{0} Nat instLENat
    (@RankwidthDomination.GraphDecomposition.width.{u_1} V inst
      (@RankwidthDomination.RankDecomposition.toGraphDecomposition.{u_1} V d hsize) G)
    (@RankwidthDomination.RankDecomposition.width.{u_1} V inst d G) := by
  exact @RankwidthDomination.RankDecomposition.toGraphDecomposition_width_le

/-- Paper C.1; component RankwidthDomination.MainResults.theorem_C_1_i. -/
theorem RankwidthPaper.result_C_1_1 :
    RankwidthDomination.Complexity.OrdinaryCountingSETH →
  ∀ (ε : Real),
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        ε →
      @LT.lt.{0} Real Real.instLT ε
          (@HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 9)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))) →
        ∀ (goal : RankwidthDomination.GraphProblem.Goal),
          @Ne.{1} RankwidthDomination.GraphProblem.Goal goal RankwidthDomination.GraphProblem.Goal.decision →
            Not
              (RankwidthDomination.GraphProblem.HasQuadraticRateAlgorithm
                RankwidthDomination.GraphProblem.Problem.domination
                RankwidthDomination.GraphProblem.GraphClass.monopolar
                RankwidthDomination.GraphProblem.Parameter.suppliedDecomposition goal
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real (nat_lit 9)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))))
                  ε)) := by
  exact @RankwidthDomination.MainResults.theorem_C_1_i

/-- Paper C.1; component RankwidthDomination.MainResults.theorem_C_1_ii. -/
theorem RankwidthPaper.result_C_1_2 :
    RankwidthDomination.Complexity.OrdinaryCountingSETH →
  ∀ (ε : Real),
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        ε →
      @LT.lt.{0} Real Real.instLT ε
          (@HDiv.hDiv.{0, 0, 0} Real Real Real
            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))) →
        ∀ (goal : RankwidthDomination.GraphProblem.Goal),
          @Ne.{1} RankwidthDomination.GraphProblem.Goal goal RankwidthDomination.GraphProblem.Goal.decision →
            Not
              (RankwidthDomination.GraphProblem.HasQuadraticRateAlgorithm
                RankwidthDomination.GraphProblem.Problem.domination
                RankwidthDomination.GraphProblem.GraphClass.monopolar
                RankwidthDomination.GraphProblem.Parameter.suppliedOrder goal
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@OfNat.ofNat.{0} Real (nat_lit 16)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                          (@Nat.instNeZeroSucc
                            (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
                  ε)) := by
  exact @RankwidthDomination.MainResults.theorem_C_1_ii

/-- Paper C.1; component RankwidthDomination.OrdinaryCountingSETH.hypothesis_iff. -/
theorem RankwidthPaper.result_C_1_3 :
    Iff RankwidthDomination.Complexity.OrdinaryCountingSETH RankwidthDomination.Complexity.CountingSETH := by
  exact @RankwidthDomination.OrdinaryCountingSETH.hypothesis_iff

/-- Paper C.1; component RankwidthDomination.ClauseDedupMachine.machine_correct. -/
theorem RankwidthPaper.result_C_1_4 :
    ∀ {n : Nat} (f : RankwidthDomination.Padding.FlatCNF n),
  @Exists.{1} Nat fun time =>
    And
      (@LE.le.{0} Nat instLENat time
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2000) (instOfNatNat (nat_lit 2000)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
                (@List.length.{0} (RankwidthDomination.Padding.FlatClause n) f))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
      (RankwidthDomination.ClauseDedupMachine.machine.outputsInTime
        (@RankwidthDomination.Padding.BinaryEncoding.formulaBits n f)
        (@RankwidthDomination.Padding.BinaryEncoding.formulaBits n
          (@RankwidthDomination.ClauseDedupMachine.dedup (RankwidthDomination.Padding.FlatClause n)
            (fun a b =>
              @Finset.decidableEq.{0} (RankwidthDomination.Padding.FlatLiteral n)
                (fun a b =>
                  @instDecidableEqProd.{0, 0} (Fin n) RankwidthDomination.Bit (instDecidableEqFin n)
                    (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b)
                a b)
            f))
        time) := by
  exact @RankwidthDomination.ClauseDedupMachine.machine_correct

/-- Paper D.1; component RankwidthDomination.SplitPerfectCode.characterization. -/
theorem RankwidthPaper.result_D_1_1.{u_1} :
    ∀ {V : Type u_1} [inst : DecidableEq.{u_1 + 1} V] {G : SimpleGraph.{u_1} V} {C I D : Finset.{u_1} V},
  @RankwidthDomination.SplitPerfectCode.SplitPartition.{u_1} V G C I →
    Iff (@RankwidthDomination.SplitPerfectCode.PerfectCode.{u_1} V G D)
      (Or
        (And (@Eq.{u_1 + 1} (Finset.{u_1} V) D I)
          (∀ (c : V),
            @Membership.mem.{u_1, u_1} V (Finset.{u_1} V) (@Finset.instMembership.{u_1} V) C c →
              @ExistsUnique.{u_1 + 1} V fun u =>
                And (@Membership.mem.{u_1, u_1} V (Finset.{u_1} V) (@Finset.instMembership.{u_1} V) I u)
                  (@SimpleGraph.Adj.{u_1} V G c u)))
        (@Exists.{u_1 + 1} V fun c =>
          And (@Membership.mem.{u_1, u_1} V (Finset.{u_1} V) (@Finset.instMembership.{u_1} V) C c)
            (And
              (∀ (u : V),
                @Membership.mem.{u_1, u_1} V (Finset.{u_1} V) (@Finset.instMembership.{u_1} V) I u →
                  Not
                      (@Membership.mem.{u_1, u_1} V (Finset.{u_1} V) (@Finset.instMembership.{u_1} V)
                        (@RankwidthDomination.SplitPerfectCode.isolated.{u_1} V G I) u) →
                    @SimpleGraph.Adj.{u_1} V G c u)
              (@Eq.{u_1 + 1} (Finset.{u_1} V) D
                (@Insert.insert.{u_1, u_1} V (Finset.{u_1} V) (@Finset.instInsert.{u_1} V inst) c
                  (@RankwidthDomination.SplitPerfectCode.isolated.{u_1} V G I)))))) := by
  exact @RankwidthDomination.SplitPerfectCode.characterization

/-- Paper D.1; component RankwidthDomination.SplitPerfectCode.candidates_eq_all. -/
theorem RankwidthPaper.result_D_1_2.{u_1} :
    ∀ {V : Type u_1} [inst : DecidableEq.{u_1 + 1} V] {G : SimpleGraph.{u_1} V} {C I : Finset.{u_1} V}
  [inst_1 : Fintype.{u_1} V],
  @RankwidthDomination.SplitPerfectCode.SplitPartition.{u_1} V G C I →
    @Eq.{u_1 + 1} (Finset.{u_1} (Finset.{u_1} V))
      (@RankwidthDomination.SplitPerfectCode.candidates.{u_1} V inst G C I)
      (@Finset.filter.{u_1} (Finset.{u_1} V) (@RankwidthDomination.SplitPerfectCode.PerfectCode.{u_1} V G)
        (fun a => Classical.propDecidable (@RankwidthDomination.SplitPerfectCode.PerfectCode.{u_1} V G a))
        (@Finset.univ.{u_1} (Finset.{u_1} V) (@Finset.fintype.{u_1} V inst_1))) := by
  exact @RankwidthDomination.SplitPerfectCode.candidates_eq_all

/-- Paper D.1; component RankwidthDomination.SplitPerfectCode.solve_correct. -/
theorem RankwidthPaper.result_D_1_3.{u_1} :
    ∀ {V : Type u_1} [inst : DecidableEq.{u_1 + 1} V] {G : SimpleGraph.{u_1} V} {C I D : Finset.{u_1} V}
  (A : @RankwidthDomination.SplitPerfectCode.AdjacencyInput.{u_1} V inst G C I),
  @RankwidthDomination.SplitPerfectCode.SplitPartition.{u_1} V G C I →
    Iff
      (@Membership.mem.{u_1, u_1} (Finset.{u_1} V) (Finset.{u_1} (Finset.{u_1} V))
        (@Finset.instMembership.{u_1} (Finset.{u_1} V))
        (@RankwidthDomination.SplitPerfectCode.represented.{u_1} V inst
          (@RankwidthDomination.SplitPerfectCode.solve.{u_1} V inst G C I A) I)
        D)
      (@RankwidthDomination.SplitPerfectCode.PerfectCode.{u_1} V G D) := by
  exact @RankwidthDomination.SplitPerfectCode.solve_correct

/-- Paper D.1; component RankwidthDomination.SplitPerfectCode.solve_number. -/
theorem RankwidthPaper.result_D_1_4.{u_1} :
    ∀ {V : Type u_1} [inst : DecidableEq.{u_1 + 1} V] {G : SimpleGraph.{u_1} V} {C I : Finset.{u_1} V}
  (A : @RankwidthDomination.SplitPerfectCode.AdjacencyInput.{u_1} V inst G C I),
  @RankwidthDomination.SplitPerfectCode.SplitPartition.{u_1} V G C I →
    @Eq.{1} Nat
      (@RankwidthDomination.SplitPerfectCode.Result.number.{u_1} V
        (@RankwidthDomination.SplitPerfectCode.solve.{u_1} V inst G C I A))
      (@Finset.card.{u_1} (Finset.{u_1} V)
        (@RankwidthDomination.SplitPerfectCode.candidates.{u_1} V inst G C I)) := by
  exact @RankwidthDomination.SplitPerfectCode.solve_number

/-- Paper D.1; component RankwidthDomination.SplitPerfectCode.solve_cost_graph_bound. -/
theorem RankwidthPaper.result_D_1_5.{u_1} :
    ∀ {V : Type u_1} [inst : DecidableEq.{u_1 + 1} V] {G : SimpleGraph.{u_1} V} {C I : Finset.{u_1} V}
  (A : @RankwidthDomination.SplitPerfectCode.AdjacencyInput.{u_1} V inst G C I) [inst_1 : Fintype.{u_1} V]
  [inst_2 : @DecidableRel.{u_1 + 1, u_1 + 1} V V (@SimpleGraph.Adj.{u_1} V G)],
  @RankwidthDomination.SplitPerfectCode.SplitPartition.{u_1} V G C I →
    @LE.le.{0} Nat instLENat
      (@RankwidthDomination.SplitPerfectCode.Result.cost.{u_1} V
        (@RankwidthDomination.SplitPerfectCode.solve.{u_1} V inst G C I A))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fintype.card.{u_1} V inst_1))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Finset.card.{u_1} (Sym2.{u_1} V)
              (@SimpleGraph.edgeFinset.{u_1} V G
                (@SimpleGraph.fintypeEdgeSet.{u_1} V G (@Sym2.instFintype.{u_1} V inst_1) inst_2)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) := by
  exact @RankwidthDomination.SplitPerfectCode.solve_cost_graph_bound

/-- Paper D.1; component RankwidthDomination.SplitPerfectCode.optimize_minimum_correct. -/
theorem RankwidthPaper.result_D_1_6.{u_1} :
    ∀ {V : Type u_1} [inst : DecidableEq.{u_1 + 1} V] {G : SimpleGraph.{u_1} V} {C I : Finset.{u_1} V}
  (A : @RankwidthDomination.SplitPerfectCode.AdjacencyInput.{u_1} V inst G C I),
  @RankwidthDomination.SplitPerfectCode.SplitPartition.{u_1} V G C I →
    ∀ {L : List.{u_1} V},
      @Eq.{u_1 + 1} (Option.{u_1} (List.{u_1} V))
          (@RankwidthDomination.SplitPerfectCode.OptimizationResult.minimum.{u_1} V
            (@RankwidthDomination.SplitPerfectCode.optimize.{u_1} V inst G C I A))
          (@Option.some.{u_1} (List.{u_1} V) L) →
        And (@RankwidthDomination.SplitPerfectCode.PerfectCode.{u_1} V G (@List.toFinset.{u_1} V inst L))
          (∀ (D : Finset.{u_1} V),
            @RankwidthDomination.SplitPerfectCode.PerfectCode.{u_1} V G D →
              @LE.le.{0} Nat instLENat (@List.length.{u_1} V L) (@Finset.card.{u_1} V D)) := by
  exact @RankwidthDomination.SplitPerfectCode.optimize_minimum_correct

/-- Paper D.1; component RankwidthDomination.SplitPerfectCode.optimize_maximum_correct. -/
theorem RankwidthPaper.result_D_1_7.{u_1} :
    ∀ {V : Type u_1} [inst : DecidableEq.{u_1 + 1} V] {G : SimpleGraph.{u_1} V} {C I : Finset.{u_1} V}
  (A : @RankwidthDomination.SplitPerfectCode.AdjacencyInput.{u_1} V inst G C I),
  @RankwidthDomination.SplitPerfectCode.SplitPartition.{u_1} V G C I →
    ∀ {L : List.{u_1} V},
      @Eq.{u_1 + 1} (Option.{u_1} (List.{u_1} V))
          (@RankwidthDomination.SplitPerfectCode.OptimizationResult.maximum.{u_1} V
            (@RankwidthDomination.SplitPerfectCode.optimize.{u_1} V inst G C I A))
          (@Option.some.{u_1} (List.{u_1} V) L) →
        And (@RankwidthDomination.SplitPerfectCode.PerfectCode.{u_1} V G (@List.toFinset.{u_1} V inst L))
          (∀ (D : Finset.{u_1} V),
            @RankwidthDomination.SplitPerfectCode.PerfectCode.{u_1} V G D →
              @LE.le.{0} Nat instLENat (@Finset.card.{u_1} V D) (@List.length.{u_1} V L)) := by
  exact @RankwidthDomination.SplitPerfectCode.optimize_maximum_correct

/-- Paper D.1; component RankwidthDomination.SplitPerfectCode.optimize_minimum_none. -/
theorem RankwidthPaper.result_D_1_8.{u_1} :
    ∀ {V : Type u_1} [inst : DecidableEq.{u_1 + 1} V] {G : SimpleGraph.{u_1} V} {C I : Finset.{u_1} V}
  (A : @RankwidthDomination.SplitPerfectCode.AdjacencyInput.{u_1} V inst G C I),
  @RankwidthDomination.SplitPerfectCode.SplitPartition.{u_1} V G C I →
    Iff
      (@Eq.{u_1 + 1} (Option.{u_1} (List.{u_1} V))
        (@RankwidthDomination.SplitPerfectCode.OptimizationResult.minimum.{u_1} V
          (@RankwidthDomination.SplitPerfectCode.optimize.{u_1} V inst G C I A))
        (@Option.none.{u_1} (List.{u_1} V)))
      (Not
        (@Exists.{u_1 + 1} (Finset.{u_1} V) fun D =>
          @RankwidthDomination.SplitPerfectCode.PerfectCode.{u_1} V G D)) := by
  exact @RankwidthDomination.SplitPerfectCode.optimize_minimum_none

/-- Paper D.1; component RankwidthDomination.SplitPerfectCode.optimize_maximum_none. -/
theorem RankwidthPaper.result_D_1_9.{u_1} :
    ∀ {V : Type u_1} [inst : DecidableEq.{u_1 + 1} V] {G : SimpleGraph.{u_1} V} {C I : Finset.{u_1} V}
  (A : @RankwidthDomination.SplitPerfectCode.AdjacencyInput.{u_1} V inst G C I),
  @RankwidthDomination.SplitPerfectCode.SplitPartition.{u_1} V G C I →
    Iff
      (@Eq.{u_1 + 1} (Option.{u_1} (List.{u_1} V))
        (@RankwidthDomination.SplitPerfectCode.OptimizationResult.maximum.{u_1} V
          (@RankwidthDomination.SplitPerfectCode.optimize.{u_1} V inst G C I A))
        (@Option.none.{u_1} (List.{u_1} V)))
      (Not
        (@Exists.{u_1 + 1} (Finset.{u_1} V) fun D =>
          @RankwidthDomination.SplitPerfectCode.PerfectCode.{u_1} V G D)) := by
  exact @RankwidthDomination.SplitPerfectCode.optimize_maximum_none

/-- Paper D.1; component RankwidthDomination.SplitPerfectCode.optimize_cost_graph_bound. -/
theorem RankwidthPaper.result_D_1_10.{u_1} :
    ∀ {V : Type u_1} [inst : DecidableEq.{u_1 + 1} V] {G : SimpleGraph.{u_1} V} {C I : Finset.{u_1} V}
  (A : @RankwidthDomination.SplitPerfectCode.AdjacencyInput.{u_1} V inst G C I),
  @RankwidthDomination.SplitPerfectCode.SplitPartition.{u_1} V G C I →
    ∀ [inst_1 : Fintype.{u_1} V] [inst_2 : @DecidableRel.{u_1 + 1, u_1 + 1} V V (@SimpleGraph.Adj.{u_1} V G)],
      @LE.le.{0} Nat instLENat
        (@RankwidthDomination.SplitPerfectCode.OptimizationResult.cost.{u_1} V
          (@RankwidthDomination.SplitPerfectCode.optimize.{u_1} V inst G C I A))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (@Fintype.card.{u_1} V inst_1))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{u_1} (Sym2.{u_1} V)
                (@SimpleGraph.edgeFinset.{u_1} V G
                  (@SimpleGraph.fintypeEdgeSet.{u_1} V G (@Sym2.instFintype.{u_1} V inst_1) inst_2)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) := by
  exact @RankwidthDomination.SplitPerfectCode.optimize_cost_graph_bound

/-- Paper 3.11; component RankwidthDomination.PaperRemarks.canonical_plus_clause. -/
theorem RankwidthPaper.result_3_11_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (split : Bool) (X : RankwidthDomination.Assignment k),
  @RankwidthDomination.Satisfies k m φ X →
    @Exists.{1} (Finset.{0} (RankwidthDomination.Vertex k m)) fun D =>
      And
        (@RankwidthDomination.Dominates.{0} (RankwidthDomination.Vertex k m)
          (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ split) D)
        (@Eq.{1} Nat (@Finset.card.{0} (RankwidthDomination.Vertex k m) D)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := by
  exact @RankwidthDomination.PaperRemarks.canonical_plus_clause

/-- Paper 3.11; component RankwidthDomination.PaperRemarks.unrestricted_outside_canonical. -/
theorem RankwidthPaper.result_3_11_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (split : Bool),
  @Exists.{1} (Finset.{0} (RankwidthDomination.Vertex k m)) fun D =>
    And
      (@RankwidthDomination.Dominates.{0} (RankwidthDomination.Vertex k m)
        (@RankwidthDomination.instDecidableEqVertex k m) (@RankwidthDomination.coreGraph k m φ split) D)
      (Not
        (@Exists.{1} (RankwidthDomination.Assignment k) fun X =>
          @Eq.{1} (Finset.{0} (RankwidthDomination.Vertex k m)) D (@RankwidthDomination.canonical k m X))) := by
  exact @RankwidthDomination.PaperRemarks.unrestricted_outside_canonical

/-- Paper 4.7; component RankwidthDomination.PaperRemarks.canonical_split_not_independent. -/
theorem RankwidthPaper.result_4_7_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (X : RankwidthDomination.Assignment k),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        k) →
    Not
      (@SimpleGraph.IsIndepSet.{0} (RankwidthDomination.Vertex k m)
        (@RankwidthDomination.coreGraph k m φ Bool.true)
        (@Finset.toSet.{0} (RankwidthDomination.Vertex k m) (@RankwidthDomination.canonical k m X))) := by
  exact @RankwidthDomination.PaperRemarks.canonical_split_not_independent

/-- Paper 4.7; component RankwidthDomination.PaperRemarks.bipCanonical_not_independent. -/
theorem RankwidthPaper.result_4_7_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (X : RankwidthDomination.Assignment k),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    Not
      (@SimpleGraph.IsIndepSet.{0} (RankwidthDomination.BipVertex k m) (@RankwidthDomination.bipGraph k m φ)
        (@Finset.toSet.{0} (RankwidthDomination.BipVertex k m) (@RankwidthDomination.bipCanonical k m X))) := by
  exact @RankwidthDomination.PaperRemarks.bipCanonical_not_independent

/-- Paper A.runtime; component RankwidthDomination.StandardAdjacencyAlgorithm.coreMatrix_correct. -/
theorem RankwidthPaper.result_A_runtime_1 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m) (split : Bool),
  @Eq.{1} (List.{0} Bool)
    (@Prod.fst.{0, 0} (List.{0} Bool) Nat
      (RankwidthDomination.StandardAdjacencyAlgorithm.coreMatrix k m split
        (@RankwidthDomination.ReductionMachine.denseInput k m φ)))
    (@RankwidthDomination.GraphProblem.adjacencyBits (RankwidthDomination.Standard.Vertex k m)
      (@RankwidthDomination.Standard.coreGraph k m φ split)
      (RankwidthDomination.StandardAdjacencyAlgorithm.labeling k m)) := by
  exact @RankwidthDomination.StandardAdjacencyAlgorithm.coreMatrix_correct

/-- Paper A.runtime; component RankwidthDomination.StandardAdjacencyAlgorithm.bipMatrix_correct. -/
theorem RankwidthPaper.result_A_runtime_2 :
    ∀ {k m : Nat} (φ : RankwidthDomination.CNF k m),
  @Eq.{1} (List.{0} Bool)
    (@Prod.fst.{0, 0} (List.{0} Bool) Nat
      (RankwidthDomination.StandardAdjacencyAlgorithm.bipMatrix k m
        (@RankwidthDomination.ReductionMachine.denseInput k m φ)))
    (@RankwidthDomination.GraphProblem.adjacencyBits (RankwidthDomination.Standard.BipVertex k m)
      (@RankwidthDomination.Standard.bipGraph k m φ)
      (RankwidthDomination.StandardAdjacencyAlgorithm.bipLabeling k m)) := by
  exact @RankwidthDomination.StandardAdjacencyAlgorithm.bipMatrix_correct

/-- Paper A.runtime; component RankwidthDomination.StandardAdjacencyAlgorithm.sigmaMatrix_correct. -/
theorem RankwidthPaper.result_A_runtime_3 :
    ∀ {k m b : Nat} (φ : RankwidthDomination.CNF k m) (clique : Bool) (P Q : Finset.{0} (Fin b))
  (R : Fin b → Finset.{0} (Fin b)),
  @Eq.{1} (List.{0} Bool)
    (@Prod.fst.{0, 0} (List.{0} Bool) Nat
      (RankwidthDomination.StandardAdjacencyAlgorithm.sigmaMatrix k m b clique
        (@RankwidthDomination.StandardAdjacencyAlgorithm.reservoirOf b P Q R)
        (@RankwidthDomination.ReductionMachine.denseInput k m φ)))
    (@RankwidthDomination.GraphProblem.adjacencyBits (RankwidthDomination.Standard.SigmaConstruction.V k m b)
      (@RankwidthDomination.Standard.SigmaConstruction.graph k m b φ clique P Q R)
      (RankwidthDomination.StandardAdjacencyAlgorithm.sigmaLabeling k m b)) := by
  exact @RankwidthDomination.StandardAdjacencyAlgorithm.sigmaMatrix_correct

/-- Paper A.runtime; component RankwidthDomination.StandardAdjacencyAlgorithm.coreMatrix_exponential. -/
theorem RankwidthPaper.result_A_runtime_4 :
    ∀ (k m : Nat) (split : Bool) (input : List.{0} Bool),
  @LE.le.{0} Nat instLENat
    (@Prod.snd.{0, 0} (List.{0} Bool) Nat
      (RankwidthDomination.StandardAdjacencyAlgorithm.coreMatrix k m split input))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 50000) (instOfNatNat (nat_lit 50000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k m)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) k))) := by
  exact @RankwidthDomination.StandardAdjacencyAlgorithm.coreMatrix_exponential

/-- Paper A.runtime; component RankwidthDomination.StandardAdjacencyAlgorithm.bipMatrix_exponential. -/
theorem RankwidthPaper.result_A_runtime_5 :
    ∀ (k m : Nat) (input : List.{0} Bool),
  @LE.le.{0} Nat instLENat
    (@Prod.snd.{0, 0} (List.{0} Bool) Nat
      (RankwidthDomination.StandardAdjacencyAlgorithm.bipMatrix k m input))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 50000) (instOfNatNat (nat_lit 50000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k m)
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) k))) := by
  exact @RankwidthDomination.StandardAdjacencyAlgorithm.bipMatrix_exponential

/-- Paper A.runtime; component RankwidthDomination.StandardAdjacencyAlgorithm.sigmaMatrix_exponential. -/
theorem RankwidthPaper.result_A_runtime_6 :
    ∀ (k m b : Nat) (clique : Bool) (data : RankwidthDomination.StandardAdjacencyAlgorithm.ReservoirData b)
  (input : List.{0} Bool),
  @LE.le.{0} Nat instLENat
    (@Prod.snd.{0, 0} (List.{0} Bool) Nat
      (RankwidthDomination.StandardAdjacencyAlgorithm.sigmaMatrix k m b clique data input))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 50000) (instOfNatNat (nat_lit 50000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k m) b)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) k))) := by
  exact @RankwidthDomination.StandardAdjacencyAlgorithm.sigmaMatrix_exponential

/-- Paper A.runtime; component RankwidthDomination.StandardAdjacencyAlgorithm.decodeSource_flat_formula. -/
theorem RankwidthPaper.result_A_runtime_7 :
    ∀ {k m : Nat}
  (f :
    RankwidthDomination.Padding.FlatCNF
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
  (hlen :
    @Eq.{1} Nat
      (@List.length.{0}
        (RankwidthDomination.Padding.FlatClause
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        f)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @Eq.{1} (Prod.{0, 0} (RankwidthDomination.StandardAdjacencyAlgorithm.Source k m) (List.{0} Bool))
    (@Prod.fst.{0, 0}
      (Prod.{0, 0} (RankwidthDomination.StandardAdjacencyAlgorithm.Source k m) (List.{0} Bool)) Nat
      (RankwidthDomination.StandardAdjacencyAlgorithm.decodeSource k m
        (@List.flatMap.{0, 0}
          (RankwidthDomination.Padding.FlatClause
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          Bool
          (@RankwidthDomination.Padding.BinaryEncoding.clauseBits
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@Monoid.toNatPow.{0} Nat Nat.instMonoid)) k
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          f)))
    (@Prod.mk.{0, 0} (RankwidthDomination.StandardAdjacencyAlgorithm.Source k m) (List.{0} Bool)
      (@RankwidthDomination.StandardAdjacencyAlgorithm.sourceOf k m
        (@RankwidthDomination.Padding.matrixCNF k m f hlen))
      (@List.nil.{0} Bool)) := by
  exact @RankwidthDomination.StandardAdjacencyAlgorithm.decodeSource_flat_formula

/-- Paper B.storage; component RankwidthDomination.B1RAM.RowCells.read_correct. -/
theorem RankwidthPaper.result_B_storage_1 :
    ∀ {k : Nat} (r : RankwidthDomination.B1RAM.RowCells k) (i : Fin k),
  @Eq.{1} (RankwidthDomination.B1RAM.Run RankwidthDomination.Bit)
    (@RankwidthDomination.B1RAM.RowCells.read k r i)
    (@RankwidthDomination.B1RAM.readRow k (@RankwidthDomination.B1RAM.RowCells.denote k r) i) := by
  exact @RankwidthDomination.B1RAM.RowCells.read_correct

/-- Paper B.storage; component RankwidthDomination.B1RAM.RowCells.zero_correct. -/
theorem RankwidthPaper.result_B_storage_2 :
    ∀ {k : Nat} (r : RankwidthDomination.B1RAM.RowCells k),
  @Eq.{1} (RankwidthDomination.B1RAM.Run Bool) (@RankwidthDomination.B1RAM.RowCells.zero k r)
    (@RankwidthDomination.B1RAM.zeroRow k (@RankwidthDomination.B1RAM.RowCells.denote k r)) := by
  exact @RankwidthDomination.B1RAM.RowCells.zero_correct

/-- Paper B.storage; component RankwidthDomination.B1RAM.RowCells.write_correct. -/
theorem RankwidthPaper.result_B_storage_3 :
    ∀ {k : Nat} (r : RankwidthDomination.B1RAM.RowCells k),
  @Eq.{1} (RankwidthDomination.B1RAM.Run (List.{0} Nat)) (@RankwidthDomination.B1RAM.RowCells.write k r)
    (@RankwidthDomination.B1RAM.writeRow k (@RankwidthDomination.B1RAM.RowCells.denote k r)) := by
  exact @RankwidthDomination.B1RAM.RowCells.write_correct

/-- Paper B.storage; component RankwidthDomination.B1RAM.storedRows_values. -/
theorem RankwidthPaper.result_B_storage_4 :
    ∀ (k : Nat),
  @Eq.{1} (List.{0} (RankwidthDomination.Row k))
    (@List.map.{0, 0} (RankwidthDomination.B1RAM.RowCells k) (RankwidthDomination.Row k)
      (@RankwidthDomination.B1RAM.RowCells.denote k)
      (@Prod.fst.{0, 0} (List.{0} (RankwidthDomination.B1RAM.RowCells k)) Nat
        (RankwidthDomination.B1RAM.storedRows k)))
    (@Prod.fst.{0, 0} (List.{0} (RankwidthDomination.Row k)) Nat (RankwidthDomination.B1RAM.rows k)) := by
  exact @RankwidthDomination.B1RAM.storedRows_values

/-- Paper B.storage; component RankwidthDomination.B1RAM.storedRows_steps. -/
theorem RankwidthPaper.result_B_storage_5 :
    ∀ (k : Nat),
  @Eq.{1} Nat
    (@Prod.snd.{0, 0} (List.{0} (RankwidthDomination.B1RAM.RowCells k)) Nat
      (RankwidthDomination.B1RAM.storedRows k))
    (@Prod.snd.{0, 0} (List.{0} (RankwidthDomination.Row k)) Nat (RankwidthDomination.B1RAM.rows k)) := by
  exact @RankwidthDomination.B1RAM.storedRows_steps

