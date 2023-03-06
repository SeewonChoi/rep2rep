import "probability.prob_parser";
import "transfer.structure_transfer";
import "server.server";
import "server.prob_renderers";

exception Error;

fun mkGoal constr (interSpace : CSpace.conSpecData) =
    let val construct = Construction.constructOf constr;
        val encodeConstructor = FiniteSet.find (fn c => "encode" = CSpace.nameOfConstructor c) (#constructors interSpace);
        val types = Option.map CSpace.csig encodeConstructor;
        val (inTypes, outType) = case types of
                                     SOME((ins, out)) => (SOME(ins),SOME(out))
                                   | NONE => (NONE, NONE)
        val tgt_type = case inTypes of
                           SOME([_, t]) => SOME(t)
                         | _ =>  NONE
        val trueTok = Option.map (CSpace.makeToken "-") outType;
        val dummy = Option.map (CSpace.makeToken "t") tgt_type;
    in case (encodeConstructor, trueTok, dummy) of
           (SOME(encodeConstructor), SOME(trueTok), SOME(dummy)) =>
           SOME(Construction.TCPair(
                     {token = trueTok, constructor = encodeConstructor},
                     [Construction.Source(construct), Construction.Source(dummy)]))
         | _ => NONE
    end;


fun getInterSpaceName srcSpaceName tgtSpaceName transferMap =
    case List.find (fn (a, b, c) => a = srcSpaceName andalso b = tgtSpaceName) transferMap of
        SOME(_, _, inter) => SOME(inter)
      | NONE => NONE;


fun transfer constr srcSpaceName tgtSpaceName transferMap spaces knowledge =
    let fun getSpace name = List.find (fn space => (#name space) = name) spaces;
        val srcSpace = getSpace srcSpaceName;
        val tgtSpace = getSpace tgtSpaceName;
        val interSpaceName = getInterSpaceName srcSpaceName tgtSpaceName transferMap;
        val intSpace = Option.mapPartial getSpace interSpaceName;
        val goal = Option.mapPartial (mkGoal constr) intSpace;
        fun err s = Result.error [Diagnostic.create Diagnostic.ERROR s []];
    in case (srcSpace, tgtSpace, intSpace, goal) of
           (SOME(s), SOME(t), SOME(i), SOME(g)) => Transfer.applyTransfer s t i knowledge constr g
         | (NONE, _, _, _) => err "No srcSpace!"
         | (_, NONE, _, _) => err "No tgtSpace!"
         | (_, _, NONE, _) => err "No intSpace!"
         | (_, _, _, NONE) => err "No goal!"
    end;

fun run_test transferMap spaces knowledge input =
    let fun area_html h = 
            let fun concatInfo (x,(y,_,_)) = "<p>"^x^"</p>\n"^y^"\n"
                val outputFile = TextIO.openOut "output/area.html";
                val _ = TextIO.output(outputFile, (concatInfo h));
                val _ = TextIO.closeOut outputFile;
                val _ = print "done.\n"
            in () end
        fun table_html h = 
            let fun concatInfo (x,(y,_,_)) = "<p>"^x^"</p>\n"^y^"\n"
                val outputFile = TextIO.openOut "output/table.html";
                val _ = TextIO.output(outputFile, (concatInfo h));
                val _ = TextIO.closeOut outputFile;
                val _ = print "done.\n"
            in () end
        fun tree_html h = 
            let fun concatInfo (x,(y,_,_)) = "<p>"^x^"</p>\n"^y^"\n"
                val outputFile = TextIO.openOut "output/tree.html";
                val _ = TextIO.output(outputFile, (concatInfo h));
                val _ = TextIO.closeOut outputFile;
                val _ = print "done.\n"
            in () end
        val () = print (input ^ "\n");
        val t = ProbParser.produce_construction input;
        val transfer = fn tgt => transfer t "bayesG" tgt transferMap spaces knowledge;
        val () = print "Area...";
        val t_area = transfer "areaDiagramG";
        val area_diagram = Result.flatmap ProbRender.drawArea t_area;
        val _ = case area_diagram of
                    Result.OK toks => area_html (hd toks)
                  | Result.ERROR errs => print ("\n" ^ (List.toString Diagnostic.message errs) ^ "\n");
        val () = print "Table...";
        val t_tabl = transfer "contTableG";
        val tabl_diagram = Result.flatmap ProbRender.drawTable t_tabl;
        val _ = case tabl_diagram of
                    Result.OK toks => table_html (hd toks)
                  | Result.ERROR errs => print ("\n" ^ (List.toString Diagnostic.message errs )^ "\n");
        val () = print "Tree...";
        val t_tree = transfer "probTreeG";
        val tree_diagram = Result.flatmap ProbRender.drawTree t_tree;
        val _ = case tree_diagram of
                    Result.OK toks => tree_html (hd toks)
                  | Result.ERROR errs => print ("\n" ^ (List.toString Diagnostic.message errs) ^ "\n");
    in () end
    handle _ => print ("FAIL: " ^ input ^ "\n");

fun test x =
    let val docs = Document.read "probability";
        val transferMap = Server.readTransferMap "transferMap";
        val spaces = Document.conSpecsDataOf docs;
        val typeSystems = Document.typeSystemsDataOf docs;
        val knowledge = Document.knowledgeOf docs;
        val () = run_test transferMap spaces knowledge x
    in () end;