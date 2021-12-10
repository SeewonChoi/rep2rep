import "transfer.search";
import "transfer.state";
import "util.logging";
import "util.random";

signature TRANSFER =
sig
  val applyCorrespondenceForGoal : State.T -> Correspondence.corr -> Relation.relationship -> State.T
  val applyCorrespondence : State.T -> Correspondence.corr -> State.T Seq.seq
  val singleStepTransfer : State.T -> State.T Seq.seq
  val structureTransfer : Knowledge.base
                            -> Type.typeSystem
                            -> Type.typeSystem
                            -> Construction.construction
                            -> Relation.relationship
                            -> State.T Seq.seq
  val iterativeStructureTransfer : Knowledge.base
                                    -> Type.typeSystem
                                    -> Construction.construction
                                    -> Relation.relationship
                                    -> State.T Seq.seq

end;

structure Transfer : TRANSFER =
struct

  exception CorrespondenceNotApplicable
  (*  *)
  fun refreshNamesOfConstruction ct D =
    let
      fun firstUnusedName Ns =
        let fun f n =
              let val vcandidate = "v_{"^(Int.toString n)^"}"
              in if List.exists (fn x => x = vcandidate) Ns then f (n+1) else "v_{"^(Int.toString n)^"}"
              end
        in f 0
        end
      val tokensInConstruction = (Construction.fullTokenSequence ct)
      val tokensInComposition = Composition.tokensOfComposition D
      val names = map CSpace.nameOfToken (tokensInComposition @ tokensInConstruction)
      fun mkRenameFunction _ [] = (fn _ => NONE)
        | mkRenameFunction Ns (y::ys) =
            let
              fun f x = if CSpace.sameTokens x y then SOME (CSpace.makeToken (firstUnusedName Ns) (CSpace.typeOfToken x))
                        else mkRenameFunction (CSpace.nameOfToken (Option.valOf (f y)) :: Ns) ys x
            in f
            end
      fun renameFunction x = mkRenameFunction names tokensInConstruction x
      val updatedConstruction = Pattern.applyMorphism renameFunction ct
    in (renameFunction, updatedConstruction)
    end

  exception Undefined
  (* The following function takes a correspondence, corr, with construct relation Rc,
     and a goal assumed to have a superRelation Rg of Rc.
     The function will try to find a generator in the given source construction that matches
     the source pattern of corr. If found, it will use the isomorphic map (from pattern to generator)
     to rename the relationships between the vertices of the source specified by the correspondence.
     It will also rename the vertices of the target pattern so that they don't clash with the
     vertices in the composition.  *)
  fun instantiateCorrForStateAndGoal corr st goal targetType =
    let
      val (sourceToken,targetToken) = (case Relation.tupleOfRelationship goal of
                                          ([x],[y],_) => (x,y)
                                        | _ => raise CorrespondenceNotApplicable) (* assumes Rc is subrelation of Rg*)
      val (rfs,rc) = Correspondence.relationshipsOf corr
      val ct = State.constructionOf st
      val T = #sourceTypeSystem st
      val patternComp = State.patternCompOf st
      val (sourcePattern,targetPattern) = Correspondence.patternsOf corr
      val targetConstructWithUpdatedType =
            CSpace.makeToken (CSpace.nameOfToken (Pattern.constructOf targetPattern)) targetType
      fun partialMorphism x = if CSpace.sameTokens x (Pattern.constructOf targetPattern)
                              then SOME targetConstructWithUpdatedType
                              else NONE
      val targetPattern' = Pattern.applyPartialMorphism partialMorphism targetPattern
      val (targetRenamingFunction, updatedTargetPattern) =
            refreshNamesOfConstruction targetPattern' patternComp
      val (sourceRenamingFunction, matchingGenerator) =
            (case Pattern.findMapAndGeneratorMatchingForToken T ct sourcePattern sourceToken of
                ((f,SOME x) ) => (f, x)
              | _ => raise CorrespondenceNotApplicable)
      fun partialFunComp f g x = (case g x of NONE => f x | SOME y => f y)
      fun srFun x = (Option.valOf o sourceRenamingFunction) x
          handle Option => (Logging.write ("\nERROR: source renaming function\n"); raise Option)
      fun trFun x = (Option.valOf o (partialFunComp targetRenamingFunction partialMorphism)) x
          handle Option => (Logging.write ("\nERROR: target renaming function\n"); raise Option)
      fun updateR (sfs,tfs,R) = (map srFun sfs, map trFun tfs, R)
      (*****)
      fun funUnion (f::L) x =
        (case (f x, funUnion L x) of
            (NONE,SOME y) => SOME y
          | (SOME y,NONE) => SOME y
          | (NONE,NONE) => NONE
          | (SOME y, SOME z) => if CSpace.sameTokens y z then SOME y else raise Undefined)
        | funUnion [] _ = NONE
      val f = Pattern.funUnion [sourceRenamingFunction,targetRenamingFunction]
      (*****)
      val updatedFoundationRelationships = map updateR rfs
      val updatedConstructRelationship = updateR rc
      val updatedPullList = map (fn (R,R',t) => (R,R',Option.valOf (targetRenamingFunction t))) (#pullList corr)
    in (fn x => if CSpace.sameTokens x targetToken then SOME (Construction.constructOf updatedTargetPattern) else NONE,
        Correspondence.declareCorrespondence {name = #name corr,
                                              sourcePattern=matchingGenerator,
                                              targetPattern=updatedTargetPattern,
                                              tokenRels=updatedFoundationRelationships,
                                              constructRel=updatedConstructRelationship,
                                              pullList = updatedPullList})
    end

  fun applyPullItem [] _ _ = []
    | applyPullItem ((x,y,R)::gs) t (R',R'',t') =
    if Relation.same R R'
    then (x,map (fn s => if CSpace.sameTokens s t then t' else s) y,R'') :: applyPullItem gs t (R',R'',t')
    else (x,y,R)::applyPullItem gs t (R',R'',t')

  exception Error
  fun applyCorrespondenceForGoal st corr goal =
    let val (sourceToken,targetToken,Rg) = (case Relation.tupleOfRelationship goal of
                                              ([x],[y],R) => (x,y,R)
                                            | _ => raise CorrespondenceNotApplicable)
        val (stcs,ttcs,Rc) = (case Correspondence.relationshipsOf corr of
                                (_,([x],[y],R)) => (x,y,R)
                              | _ => (print "oh no!";raise Error))
        val sT = #sourceTypeSystem st
        val tT = #targetTypeSystem st
        val typeOfTargetTokenInGoal = CSpace.typeOfToken targetToken
        val typeOfTargetConstructInCorr = CSpace.typeOfToken ttcs
        fun minType typSys (ty1,ty2) =
              if (#subType typSys) (ty1,ty2) then ty1
              else if (#subType typSys) (ty2,ty1) then ty2
              else raise CorrespondenceNotApplicable
        val (f,instantiatedCorr) =
              if Knowledge.subRelation (State.knowledgeOf st) Rc Rg
                 andalso Pattern.tokenMatches sT sourceToken stcs
              then instantiateCorrForStateAndGoal corr st goal (minType tT (typeOfTargetTokenInGoal, typeOfTargetConstructInCorr))
              else raise CorrespondenceNotApplicable
        val (_,targetPattern) = Correspondence.patternsOf instantiatedCorr
      (*  val _ = print ((CSpace.nameOfToken targetToken) ^ CSpace.nameOfToken(Pattern.constructOf targetPattern) ^ "\n")*)
        val (rfs,rc) = Correspondence.relationshipsOf instantiatedCorr
        val patternComp = State.patternCompOf st
        val updatedPatternComp = if Composition.isPlaceholder patternComp
                                 then Composition.initFromConstruction targetPattern
                                 else Composition.attachConstructionAt patternComp targetPattern targetToken
        val transferProof = State.transferProofOf st
        val updatedTransferProof' = TransferProof.attachCorrAt instantiatedCorr goal transferProof
        val updatedTransferProof = TransferProof.attachCorrPulls instantiatedCorr targetToken updatedTransferProof'
        val gs' = State.goalsOf (State.replaceGoal st goal rfs)
        fun applyPullList [] = gs'
          | applyPullList (pi::pL) = applyPullItem (applyPullList pL) targetToken pi
        val updatedGoals = applyPullList (#pullList instantiatedCorr)
        val _ = if not (null (#pullList instantiatedCorr)) andalso List.allZip Relation.sameRelationship gs' updatedGoals
                then raise CorrespondenceNotApplicable else ()
        val stateWithUpdatedGoals = State.updateGoals st updatedGoals
        val stateWithUpdatedProof = State.updateTransferProof stateWithUpdatedGoals updatedTransferProof
    in State.applyPartialMorphismToCompAndGoals f (State.updatePatternComp stateWithUpdatedProof updatedPatternComp)
    end

  (* The function idempotencyOnGoals assumes that the relations being dumped are type-deterministic *)
  fun idempotencyOnGoals st =
    let fun isomorphic (x,y,R) (x',y',R') = List.allZip CSpace.sameTokens y y' andalso
                                            List.allZip CSpace.tokensHaveSameType x x' andalso
                                            Relation.same R R'
        fun rg (g::gs) =
            let val (keep,dump) = rg gs
            in if List.exists (isomorphic g) keep
               then (keep,g::dump)
               else (g::keep,dump)
            end
          | rg [] = ([],[])
        fun updateTransferProof (g::gs) = TransferProof.dump g (updateTransferProof gs)
          | updateTransferProof [] = State.transferProofOf st
        val (keep,dump) = rg (State.goalsOf st)
        val stateWithUpdatedGoals = State.updateGoals st keep
    in State.updateTransferProof stateWithUpdatedGoals (updateTransferProof dump)
    end

  fun applyCorrespondence st corr =
    let val newSt = idempotencyOnGoals st
        fun ac [] = Seq.empty
          | ac (g::gs) = (Seq.cons (applyCorrespondenceForGoal newSt corr g) (ac gs)
                            handle CorrespondenceNotApplicable => ac gs)
        (***)
    in ac (State.goalsOf newSt)
    end

  fun singleStepTransfer st =
    let val corrs = #correspondences (State.knowledgeOf st)
    in Seq.maps (applyCorrespondence st) corrs
    end

  exception BadGoal

  (* every element of goals should be of the form ([vi1,...,vin],[vj1,...,vjm],R)*)
  fun structureTransferTac h ign forget state =
      (*Search.depthFirst singleStepTransfer limit initialState*)
      (*Search.graphDepthFirst singleStepTransfer eq limit initialState*)
      (*Search.breadthFirstSortAndIgnore singleStepTransfer heuristic6 ign' initialState*)
      (*Search.breadthFirstSortIgnoreForget singleStepTransfer heuristic4 ign' forget initialState*)
      (*Search.depthFirstSortAndIgnore singleStepTransfer heuristic4 ign' initialState*)
      (*Search.depthFirstSortIgnoreForget singleStepTransfer heuristic4 ign' forget initialState*)
      (*Search.bestFirstSortAndIgnore singleStepTransfer heuristic6 ign' initialState*)
      Search.bestFirstSortIgnoreForget singleStepTransfer h ign forget state

    (* every element of goals should be of the form ([vi1,...,vin],[vj1,...,vjm],R)*)
fun structureTransfer KB sourceT targetT ct goal =
  let
    val t = (case Relation.tupleOfRelationship goal of
                (_,[x],_) => x
              | _ => raise BadGoal)
    val initialState = State.make {sourceTypeSystem = sourceT,
                                    targetTypeSystem = targetT,
                                    transferProof = TransferProof.ofRelationship goal,
                                    construction = ct,
                                    originalGoal = goal,
                                    goals = [goal],
                                    composition = Composition.makePlaceholderComposition t,
                                    knowledge = KB}
    fun heuristic1 (st,st') =
      let val D = State.patternCompOf st
          val D' = State.patternCompOf st'
      in Int.compare ((Composition.size D'), (Composition.size D))
      end
    fun heuristic2 (st,st') =
      let val gs = State.goalsOf st
          val gs' = State.goalsOf st'
          val D = State.patternCompOf st
          val D' = State.patternCompOf st'
      in Real.compare (real(Composition.size D') * Math.ln(real(length gs + 1)), real(Composition.size D) * Math.ln(real(length gs' + 1)))
      end
    fun heuristic3 (st,st') =
      let val gs = State.goalsOf st
          val gs' = State.goalsOf st'
      in Int.compare (length gs,length gs')
      end
    fun opposite LESS = GREATER | opposite EQUAL = EQUAL | opposite GREATER = LESS
    fun heuristic4 (st,st') =
      let val gs = State.goalsOf st
          val gs' = State.goalsOf st'
          val gsn = length gs
          val gsn' = length gs'
          val D = State.patternCompOf st
          val D' = State.patternCompOf st'
          val P = Int.compare (Composition.size D,Composition.size D')
      in if gsn = 0 andalso gsn' = 0 then P
         else if gsn > 0 andalso gsn' > 0 andalso P <> EQUAL then opposite P
         else Int.compare (gsn,gsn')
      end
    fun heuristic5 _ =
      let val x1 = MLtonRandom.rand ()
          val X2 = map MLtonRandom.rand [(),(),(),(),(),(),(),(),(),()]
          fun le x = List.all (fn y => x < y) X2
      in if le x1 then LESS else GREATER
      end
    fun heuristic6 (st,st') =
      let val gsn = length (State.goalsOf st)
          val gsn' = length (State.goalsOf st')
      in if (gsn = 0 andalso gsn' = 0) orelse (gsn > 0 andalso gsn' > 0) then heuristic5 (st,st')
         else Int.compare (gsn,gsn')
      end
    fun heuristicIS (st,st') =
      let val gsn = length (State.goalsOf st)
          val gsn' = length (State.goalsOf st')
          val tproof = State.transferProofOf st
          val tproof' = State.transferProofOf st'
          val strength = Knowledge.strengthOf (State.knowledgeOf st)
      in if (gsn = 0 andalso gsn' = 0) orelse (gsn > 0 andalso gsn' > 0)
         then Real.compare (TransferProof.multiplicativeIS strength tproof',TransferProof.multiplicativeIS strength tproof)
         else Int.compare (gsn,gsn')
      end
    val limit = 999
    fun eq (st,st') = List.isPermutationOf (uncurry Relation.sameRelationship) (State.goalsOf st) (State.goalsOf st')
    fun eq' (st,st') = TransferProof.similar (State.transferProofOf st) (State.transferProofOf st')
    (*Composition.pseudoSimilar (State.patternCompOf st) (State.patternCompOf st')
                andalso List.isPermutationOf (uncurry Relation.stronglyMatchingRelationships) (State.goalsOf st) (State.goalsOf st')*)
    fun ign (st,L) = List.length (State.goalsOf st) > 30 orelse length L > limit orelse List.exists (fn x => eq (x,st)) L
    fun ign' (st,L) = List.length (State.goalsOf st) > 20
                orelse length L > limit
              (*  orelse List.exists Relation.relationshipIsFalse (State.goalsOf st)*)
                orelse Composition.size (State.patternCompOf st) > 40
                orelse List.exists (fn x => eq' (x,st)) L
                orelse not (Composition.unistructurable (State.targetTypeSystemOf st) (State.patternCompOf st))
    fun forget st = List.length (State.goalsOf st) < 0
  in structureTransferTac heuristicIS ign' forget initialState
  end

  fun v2t t =
    let val tok = CSpace.nameOfToken t
        val typ = CSpace.typeOfToken t
        fun vt (x::xs) = if x = #"v" then #"t"::xs else x::xs
          | vt [] = []
    in SOME (CSpace.makeToken (String.implode (vt (String.explode tok))) typ)
    end

  exception Nope
  fun iterativeStructureTransfer KB typeSystem ct goal =
    let
      val t = (case Relation.tupleOfRelationship goal of
                  (_,[x],_) => x
                | _ => raise BadGoal)
      val initialState = State.make {sourceTypeSystem = typeSystem,
                                      targetTypeSystem = typeSystem,
                                      transferProof = TransferProof.ofRelationship goal,
                                      construction = ct,
                                      originalGoal = goal,
                                      goals = [goal],
                                      composition = Composition.makePlaceholderComposition t,
                                      knowledge = KB}
      val (x,y,R) = Relation.tupleOfRelationship goal
      fun updateState (C as {composition,goals,...}) =
        let val newConstruction = (case Composition.resultingConstructions composition of [c] => Pattern.applyMorphism v2t c | _ => raise Nope)
            val newConstruct = Construction.constructOf newConstruction
            val newGoal = Relation.makeRelationship ([newConstruct],y,R)
            val _ = if length goals > 0 then raise Nope else ()
        in State.make {sourceTypeSystem = typeSystem,
                      targetTypeSystem = typeSystem,
                      transferProof = TransferProof.ofRelationship newGoal,
                      construction = newConstruction,
                      originalGoal = newGoal,
                      goals = [newGoal],
                      composition = Composition.makePlaceholderComposition newConstruct,
                      knowledge = KB} handle Nope => (print "nope";C)
        end
      fun heuristicIS (stx,st') =
        let val gsn = length (State.goalsOf stx)
            val gsn' = length (State.goalsOf st')
            val tproof = State.transferProofOf stx
            val tproof' = State.transferProofOf st'
            val strength = Knowledge.strengthOf (State.knowledgeOf stx)
        in if (gsn = 0 andalso gsn' = 0) orelse (gsn > 0 andalso gsn' > 0)
           then Real.compare (TransferProof.multiplicativeIS strength tproof',TransferProof.multiplicativeIS strength tproof)
           else Int.compare (gsn,gsn')
        end
      val limit = 3
      fun similar x y = Composition.pseudoSimilar (State.patternCompOf x) (State.patternCompOf y)
      fun eqST (st,st') = TransferProof.similar (State.transferProofOf st) (State.transferProofOf st')
      fun ign (st,L) = List.exists (fn x => similar x st) L
      fun ignST (st,L) = List.length (State.goalsOf st) > 20
                  orelse length L > 1999
                (*  orelse List.exists Relation.relationshipIsFalse (State.goalsOf st)*)
                  orelse Composition.size (State.patternCompOf st) > 40
                  orelse List.exists (fn x => eqST (x,st)) L
                  orelse not (Composition.unistructurable (State.targetTypeSystemOf st) (State.patternCompOf st))
      fun forget st = List.length (State.goalsOf st) > 0
      fun orderResults s = case Seq.pull s of SOME (x,xq) => Seq.insertManyNoRepetition x (orderResults xq) heuristicIS (uncurry similar) | NONE => Seq.empty
      val ST = Seq.take limit o (structureTransferTac heuristicIS ignST forget)
      val results = Seq.map (Search.bestFirstSortIgnoreForget (ST o updateState) heuristicIS ign forget) (ST initialState)
    in orderResults results
    end

end;
