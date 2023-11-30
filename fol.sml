structure Fol  =
struct
  datatype term = VAR of string
  | FUN of string * term list
  | CONST of string (* for generated constants only *)
  datatype Pred = FF (* special constant for closing a tableau path *)
  | ATOM of string * term list
  | NOT of Pred
  | AND of Pred * Pred
  | OR of Pred * Pred
  | COND of Pred * Pred
  | BIC of Pred * Pred
  | ITE of Pred * Pred * Pred
  | ALL of term * Pred
  | EX of term * Pred
  type PI = (Pred * int)

  datatype Argument = HENCE of Pred list * Pred
  exception NotVAR (* Binding term in a quantified formula is not a variable *)
  exception NotWFT (* term is not well-formed *)
  exception NotWFP (* predicate is not well-formed *)
  exception NotWFA (* argument is not well-formed *)
  exception NotClosed (* a formula is not closed *)
  val fns = ref [] : (string*int) list ref (*Seen function names and their arity*)
  val atoms = ref [] : (string*int) list ref (*Seen atomic predicate and their arity*)

  fun find(x, l) = (List.find (fn (s,_) => x = s) l) 
  fun find2(x, l) = (List.find (fn s => x = s) l) 

  fun checkTerm vlist t =
  case t of 
    VAR(x) => if find2(x,vlist) = NONE then raise NotClosed else ()
  | FUN(x, tlist) => 
      let 
          val res = getOpt(find(x,!fns), (x,~1))
          val n = #2 (res)
        in
          if (n = ~1) then 
            if not (find2(x,vlist) = NONE andalso find(x,!atoms) = NONE) then raise NotWFA else
            fns := (x, (List.length tlist)):: !fns
          else 
            if n = (List.length tlist) then  (app (checkTerm vlist) tlist)
            else raise NotWFT
      end
    | _ => ()
    
  fun checkPred vlist p =  
  case p of 
  ATOM(x,t) =>
    let 
      val res = getOpt(find(x,!atoms), (x,~1))
      val n = #2 (res)
    in
      if (n = ~1) then 
        if not (find2(x,vlist) = NONE andalso find(x,!fns) = NONE) then raise NotWFA else
        atoms := (x, (length t)):: !atoms
      else 
        if n = (length t) then  (app (checkTerm vlist) t)
        else raise NotWFP
    end
  | NOT(q) => (checkPred vlist q )
  | AND(p1,p2) => ((checkPred vlist p1);(checkPred vlist p2))
  | OR(p1,p2) => ((checkPred vlist p1 );(checkPred vlist p2))
  | COND(p1,p2) => ((checkPred vlist p1);(checkPred vlist p2))
  | BIC(p1,p2) => ((checkPred vlist p1);(checkPred vlist p2))
  | ITE(p1, p2, p3) => ((checkPred vlist p1);(checkPred vlist p2);(checkPred vlist p3))
  
  
  | EX(v,p1) =>  (case v of 
                  VAR(x) => if not (find(x,!fns) = NONE andalso find(x,!atoms) = NONE) then raise NotWFA else
                            (checkPred (x::vlist) p1)
                  | _ => raise NotVAR)
  | ALL(v, p1) => (case v of 
                  VAR(x) => if not (find(x,!fns) = NONE andalso find(x,!atoms) = NONE) then raise NotWFA else
                            (checkPred (x::vlist) p1)
                  | _ => raise NotVAR)
  
  fun check(a: Argument): unit = 
      case a of 
        HENCE(hyp, conc) => ((app (checkPred []) hyp); (checkPred [] conc))


(* helper functions *)
 val varnum = ref 0 : int ref
 val cnum = ref 0 : int ref
 val numNode = ref 0 : int ref 
 val nodes =ref (Queue.mkQueue()) : (Pred * int) Queue.queue ref
 val unifyEdges = Queue.mkQueue() : (int * int) Queue.queue
 val conjEdges = Queue.mkQueue() : (int * int) Queue.queue
 val tableauEdges = Queue.mkQueue() : (int * int) Queue.queue

  fun getConst(cnum) = 
    let val cur = !cnum in 
    (cnum := !cnum + 1; Int.toString(cur))
    end
  fun getNewVar(varnum) = 
    let val cur = !varnum in 
    (varnum := !varnum + 1; Int.toString(cur))
    end
  fun neg(f) =
   case f of 
        NOT(x) => x
      | x => NOT(x)

  fun addNode(f : Pred): int = 
    let 
      val nodeid = ! numNode
    in 
      (Queue.enqueue(!nodes, (f,nodeid));(numNode := !numNode + 1) ;nodeid)
    end

  fun addTedge(a) = Queue.enqueue(tableauEdges, a)
  fun addUedge(a) = Queue.enqueue(unifyEdges, a)
  fun addCedge(a) = Queue.enqueue(conjEdges, a)

  fun simplifyFormula (a: Argument) : PI =
  case a of 
    HENCE([], conc) => let val ret = NOT(conc) in 
       (ret, addNode(ret))
      end
    | HENCE(hyp, conc) => (let
      val cnj = foldr (fn (x,y) => AND(x,y)) (hd hyp) (tl hyp)
      val ret = AND(cnj, NOT(conc))
      in 
      (ret, addNode(ret))
      end)
  
  fun predReducible(p : Pred): bool =
  case p of 
    ATOM(s,t) => false
  | NOT(ATOM(s,t)) => false 
  | f => true 

  fun chain(p : Pred): bool = 
  case p of 
  AND(x,y) => true
  | NOT(OR(x,y)) => true
  | NOT(COND(x,y)) => true
  | f => false

  fun existential(p: Pred): bool = 
  case p of 
    NOT(ALL(x,t)) => true
  | EX(x,t) => true
  | f => false 

  fun universal(p: Pred): bool = 
  case p of 
      ALL(x,t) => true
    | NOT(EX(x,t)) => true
    | f => false

  fun branch(p : Pred): bool = 
    not(chain(p)) andalso not(existential(p)) andalso not(universal(p)) andalso predReducible(p)

  fun h tyfn (x,y) = tyfn(x)
    

  fun TtoString(t : term): string = 
  case t of 
  VAR(x) => x
  | FUN(f,tt) => if length(tt) = 0 then f 
                else 
                  let 
                    val strs = (map TtoString tt)
                    val allterms = List.foldl (fn (xx,y) => xx ^ "," ^ y) (hd strs) (tl strs)
                  in 
                  f ^ "(" ^ allterms ^ ")" 
                  end
  | CONST(c) => c

  fun br s = "(" ^ s ^ ")"
  fun PtoString( f : Pred ): string = 
  case f of 
  ATOM(x,tt) => if length(tt) = 0 then x
                else 
                  let 
                    val strs = (map TtoString tt)
                    val allterms = List.foldl (fn (k,y) => k ^ "," ^ y) (hd strs) (tl strs)
                  in 
                  x ^ "(" ^ allterms ^ ")" 
                  end
  | NOT(q) => "\\neg " ^ br(PtoString(q))
  | AND(p1,p2) => br(PtoString(p1)) ^ " \\wedge " ^ br(PtoString(p2))
  | OR(p1,p2) => br(PtoString(p1)) ^ " \\vee " ^ br(PtoString(p2))
  | COND(p1,p2) => br(PtoString(p1)) ^ " \\rightarrow " ^ br(PtoString(p2))
  | BIC(p1,p2) =>  br(PtoString(p1)) ^ " \\leftrightarrow " ^ br(PtoString(p2))
  | ITE(p1, p2, p3) => br(PtoString(p1)) ^" ? "^ br(PtoString(p2)) ^ " : " ^ br(PtoString(p3))
  | FF => "\\bot"
  | EX(VAR(x), p1) => "\\exists "^x^"["^PtoString(p1)^"]"
  | ALL(VAR(x), p1) =>  "\\forall "^x^"["^PtoString(p1)^"]"
  fun selectForm(branch0) = 
  let 
    val c = (List.find (h chain) branch0)
  in 
  if not(c = NONE) then valOf(c)
  else 
    let 
       val b = (List.find (h branch) branch0)
    in 
    if not(b = NONE) then valOf(b)
    else
      let val e = (List.find (h existential) branch0)
      in 
      if not(e = NONE) then valOf(e) 
      else 
        let val u = (List.find (h universal) branch0)
        in 
        if not(u = NONE) then valOf(u) 
        else hd(branch0)
        end
      end
    end
  end

  fun computepi(flist, idlist) = 
  case flist of 
  [] => []
  | x::xs => 
    (case idlist of 
     [] => []
    | y ::ys => (x,y) :: computepi(xs,ys))

  fun replace (prop, formulaList, branch) = 
  let 
    fun helperf(p, f, b, buff) =
      case b of 
        [] => []
      | (a,b) :: xs => if p = a then buff @ f @ xs   
                    else helperf(p, f, xs, buff @ [(a,b)])
    in 
  helperf(prop, formulaList, branch, [])
  end

  fun getBranch(pi, flist, branch0, lastnode, rep, blue): (((Pred*int)list * int)*((Pred*int)list))list = 
    let val ids = (map addNode flist)
        val (p,i) = pi
    in 
    addTedge((lastnode, hd(ids)));
    if blue then addUedge((i,hd ids)) else ();
    if length(flist) = 2 then addTedge(hd(ids), hd(tl(ids)))
    else ();
    let 
      val new = computepi(flist,ids)
      in
    if rep then
    [((replace(p, new, branch0), List.last ids), new)]
    else
    [((new@replace(p, [], branch0)@[pi], List.last ids), new)]
    end
    end
  
  fun substTerm sublist term = 
  case term of 
  VAR(x) => let val pres = (List.find (fn (x,y) => x = term) sublist)
                        in 
                        if pres = NONE then VAR(x)
                        else (#2 (valOf pres))   end        
  | FUN(f, tt) => FUN(f, (map (substTerm sublist) tt)) 
  | CONST(c) => CONST(c)

  fun subst sublist formula = 
    if sublist = [] then formula
    else
    case formula of 
      ATOM(x,tt) => ATOM(x, (map (substTerm sublist) tt))
      | NOT(q) => NOT(subst sublist q)
      | AND(p1,p2) => AND(subst sublist p1, subst sublist p2)
      | OR(p1,p2) => OR(subst sublist p1, subst sublist p2)
      | COND(p1,p2) => COND(subst sublist p1, subst sublist p2)
      | BIC(p1,p2) =>  BIC(subst sublist p1, subst sublist p2)
      | ITE(p1, p2, p3) => ITE(subst sublist p1, subst sublist p2, subst sublist p2)
      | FF => FF
      | EX(term, ep) => let val pres = (List.find (fn x => x = term) (map #1 sublist))
                        in 
                        if pres = NONE then EX(term, (subst sublist ep))
                        else 
                        let val slist2 = (List.filter (fn x => not((#1 x) = term)) sublist)
                        in
                        EX(term, (subst slist2 ep))
                        end end
      | ALL(term, ep) => let val pres = (List.find (fn x => x = term) (map #1 sublist))
                        in 
                        if pres = NONE then ALL(term, (subst sublist ep))
                        else 
                        let val slist2 = (List.filter (fn x => not((#1 x) = term)) sublist)
                        in
                        ALL(term, (subst slist2 ep))
                        end end

  fun freeVarT l r term  = 
  case term of
  VAR(x) => let val pres = (List.find (fn y => y = term) l)
                        in 
                        if pres = NONE then (r:= term::(!r))
                        else ()  end       
  | FUN(f, tt) => (app (freeVarT l r) tt)
  | CONST(c) => ()

  fun freeVar(formula, r, l) = 
  case formula of 
  ATOM(x,tt) => (app (freeVarT l r) tt)
  | NOT(q) => freeVar(q,r,l)
  | AND(p1,p2) => (freeVar(p1,r,l); freeVar(p2,r,l))
  | OR(p1,p2) => (freeVar(p1,r,l); freeVar(p2,r,l))
  | COND(p1,p2) => (freeVar(p1,r,l); freeVar(p2,r,l))
  | ITE(p1, p2, p3) => (freeVar(p1,r,l); freeVar(p2,r,l); freeVar(p3,r,l))
  | FF => ()
  | EX(term, ep) => (freeVar(ep, r, term::l))
  | ALL(term, ep) => (freeVar(ep, r, term::l))
  | BIC(p1,p2) => (freeVar(p1,r,l); freeVar(p2,r,l))

  fun removeCopies(l, a) =
  case l of 
  [] => l
  | x :: xs =>  
    let val pres = (List.find (fn y => y = x) a)
                        in 
                        if pres = NONE then removeCopies(tl l, x :: a)
                        else removeCopies(tl l, a)  end  

  fun branchOf(pi, branch0, lastnode) = 
  let
   val (p,_) = pi
  in 
  case p of 
    NOT(NOT(f)) => getBranch(pi, [f], branch0, lastnode, true, false) 
  | NOT(AND(f1, f2)) => 
    let 
      val v1 = getBranch(pi, [NOT(f1)], branch0, lastnode, true, false)
      val v2 = getBranch(pi, [NOT(f2)], branch0, lastnode, true, false)
    in 
      ( v1 @ v2 )
    end 
  | NOT(OR(f1, f2)) => getBranch(pi, [NOT(f1), NOT(f2)], branch0, lastnode, true, false) 
  | NOT(COND(f1, f2)) => getBranch(pi, [f1, NOT(f2)], branch0, lastnode, true, false)
  | NOT(BIC(f1,f2)) => 
    let 
        val v1 = getBranch(pi, [f1, NOT(f2)], branch0, lastnode, true, false)
        val v2 = getBranch(pi, [NOT(f1), f2], branch0, lastnode, true, false)
      in 
        ( v1 @ v2 )
    end 
  | NOT(ITE(f1, f2, f3)) => 
    let 
        val v1 = getBranch(pi, [f1, NOT(f2)], branch0, lastnode, true, false)
        val v2 = getBranch(pi, [NOT(f1), NOT(f3)], branch0, lastnode, true, false)
      in 
        ( v1 @ v2 )
    end 
  | AND(f1, f2) => getBranch(pi, [f1, f2], branch0, lastnode, true, false)
  | OR(f1, f2) => let 
        val v1 = getBranch(pi, [f1], branch0, lastnode, true, false)
        val v2 = getBranch(pi, [f2], branch0, lastnode, true, false)
      in 
        ( v1 @ v2 )
    end 
  | COND(f1, f2) => 
    let 
        val v1 = getBranch(pi, [NOT(f1)], branch0, lastnode, true, false)
        val v2 = getBranch(pi, [f2], branch0, lastnode, true, false)
      in 
        ( v1 @ v2 )
    end 
  | BIC(f1, f2) =>
    let 
        val v1 = getBranch(pi, [f1, f2], branch0, lastnode, true, false)
        val v2 = getBranch(pi, [NOT(f1), NOT(f2)], branch0, lastnode, true, false)
      in 
        ( v1 @ v2 )
    end
  | ITE(f1, f2, f3) =>
     let 
        val v1 = getBranch(pi, [f1, f2], branch0, lastnode, true, false)
        val v2 = getBranch(pi, [NOT(f1), f3], branch0, lastnode, true, false)
      in 
        ( v1 @ v2 )
    end
  | EX(x, f1) => 
    let 
      val r = ref [] : term list ref
      val u = freeVar(f1, r, []);
      val fv = removeCopies(!r, []);
      val newc = getConst(cnum);
      val newf = if fv = [] then (subst [(x, CONST("g" ^ newc))] f1)
                else (subst [(x, FUN("g"^newc, fv))] f1)
    in 
      getBranch(pi, [newf], branch0, lastnode, true, true)
    end
  | NOT(ALL(x,f1)) => 
  let 
      val r = ref [] : term list ref
      val u = freeVar(f1, r, []);
      val fv = removeCopies(!r, []);
      val newc = getConst(cnum);
      val newf = if fv = [] then (subst [(x, CONST("g" ^ newc))] (NOT(f1)))
                else (subst [(x, FUN("g"^newc, fv))] (NOT(f1)))
    in 
      getBranch(pi, [newf], branch0, lastnode, true, true)
    end
  | ALL(x,f1) => 
    let 
      val newv = getNewVar(varnum)
      val t = VAR("v"^newv)
      val newf = (subst [(x, t)] f1)
    in 
    getBranch(pi, [newf], branch0, lastnode, false, true)
    end
  | NOT(EX(x,f1)) => 
    let 
      val newv = getNewVar(varnum)
      val t = VAR("v"^newv)
      val newf = (subst [(x, t)] (NOT(f1)))
    in 
    getBranch(pi, [newf], branch0, lastnode, false, true)
    end
  end

  fun occurs v t = 
    let val temp = ref []: term list ref
        val vars = (freeVarT [] temp t)
    in
    not ((List.find (fn x => x = v) (!temp)) = NONE)
    end

  fun unifyTerms [] [] = (true,[])
  | unifyTerms t1 t2 = 
  let val (b, sub) = 
    (case (hd t1, hd t2) of
    (CONST(c1), CONST(c2)) => if c1 = c2 then (true,[]) else (false,[])
    | (FUN(g1,tt1), FUN(g2,tt2)) => if g1 = g2 then (unifyTerms tt1 tt2) else (false,[])
    | (VAR(x), VAR(y)) => (true, [(VAR(x), VAR(y))])
    | (VAR(x), CONST(c)) => (true, [(VAR(x), CONST(c))])
    | (CONST(c), VAR(x)) => (true, [(VAR(x), CONST(c))])
    | (VAR(x), FUN(g, tt)) => if not(occurs (VAR(x)) (FUN(g,tt))) then  (true, [(VAR(x), FUN(g, tt))])
                              else (false, [])
    | (FUN(g, tt), VAR(x)) => if not(occurs (VAR(x)) (FUN(g,tt))) then  (true, [(VAR(x), FUN(g, tt))])
                              else (false, [])
    | _ => (false, []))
    in 
    if not b then (false,[]) 
    else 
      let val subTl1 = (map (substTerm sub) (tl t1))
          val subTl2 = (map (substTerm sub) (tl t2))
          val (nb, nsub) = (unifyTerms subTl1 subTl2)
      in 
      (nb, sub @ nsub)
      end  
    end

  fun unify [] [] = (true,[])
  | unify f1 f2 = 
  let val (b, sub) = 
    (case (hd f1, hd f2) of 
     (ATOM(x1,t1), ATOM(x2,t2)) => if x1 = x2 then (unifyTerms t1 t2) else (false,[])
    | (NOT(x1),NOT(x2)) => (unify [x1] [x2])
    | (AND(x1,x2),AND(x3,x4)) => (unify [x1,x2] [x3,x4])
    | (OR(x1,x2),OR(x3,x4)) => (unify [x1,x2] [x3,x4])
    | (COND(x1,x2),COND(x3,x4)) => (unify [x1,x2] [x3,x4])
    | (BIC(x1,x2),BIC(x3,x4)) => (unify [x1,x2] [x3,x4])
    | (ITE(x1,x2,x3),ITE(x4,x5,x6)) => (unify [x1,x2,x3] [x4,x5,x6])
    | _ => (false, []))
    in 
    if not b then (false, [])
    else 
      let val subTl1 = (map (subst sub) (tl f1))
          val subTl2 = (map (subst sub) (tl f2))
          val (nb, nsub) = (unify subTl1 subTl2)
      in 
      (nb, sub @ nsub)
      end
    end

  fun closableWith b0 (f0,id) =
  let val (k,l) = b0 in
      if k = [] then (false,[]) else
      let val (first,somid) = (hd k) in
      case (unify [first] [neg(f0)]) of
      (false,_) => (closableWith ((tl k),l) (f0,id))
      | (true, sub) => ((addCedge(somid,id));(true,sub))
      end
  end

  fun closable b0 flist = if flist = [] then (false,[])
  else case (closableWith b0 (hd flist)) of
  (false,_) => (closable b0 (tl flist))
  | (true, sub) => (true, sub)

  fun changeBranch sub (br1,br2) =  ((map (fn (x,y) => ((subst sub x),y)) (br1)), (br2))
  fun changeBranches sub brlist = (map (changeBranch sub) brlist)
  fun changeBranches2 sub br =  (map (fn (x,y) => (changeBranch sub x, (map (fn (h,j) => ((subst sub h),j)) y))) br)

  fun checkOpen [] oldbr = oldbr 
  | checkOpen newbr oldbr = 
    let val comb = (hd newbr) : ((((Pred*int)list)*(int))*((Pred*int)list))
        val (b0, formulaList) = comb
        val (close, sub) = (closable b0 formulaList)
    in 
    if close then 
      let val (br, lastnode) = b0 
          val id = addNode(FF)
          val u = addTedge(lastnode, id)
      in 
        (nodes := (Queue.map (fn (x,y) => ((subst sub x),y)) (!nodes));
        (checkOpen (changeBranches2 sub (tl newbr)) (changeBranches sub (oldbr))))
      end
    else 
      (checkOpen (tl newbr) (b0 :: oldbr))
    end
  
  fun mktableauH p = 
  case p of 
  [] => []
  | branchList => 
    let 
      val branch0 = #1 (hd branchList)
      val lastnode = #2 (hd branchList)
    in 
    case (List.find (h predReducible) branch0) of 
       SOME(prop) => 
       let val sel = selectForm(branch0)
          val branchNnewform = branchOf(sel, branch0, lastnode)
          val branches = (map #1 branchNnewform)
          val newForms = (map #2 branchNnewform)
        in 
        mktableauH(checkOpen branchNnewform (tl branchList))
       end
      | NONE => branch0    
    end

  fun mktableau a = mktableauH([([simplifyFormula(a)],0)])
  val ar = HENCE([ALL(VAR("x"), COND(ATOM("p", [VAR("x")]), ATOM("q", [VAR("x")])))], COND(ALL(VAR("x"), ATOM("p", [VAR("x")])), ALL(VAR("x"), ATOM("q", [VAR("x")]))))
      val l = (mktableau ar)

  fun dotifyNode node = 
  let val (p,i) = node
      val num = Int.toString(i)
  in 
  num ^ " [texlbl=\"\\underline{" ^ num ^ ". $" ^ PtoString(p) ^ "$}\"];\n"
  end
  fun dotifyEdge(edge) = 
  let val (s,d) = edge in 
  Int.toString(s) ^ " -> " ^ Int.toString(d) ^ ";\n"
  end
  val outStream = TextIO.openOut("tableau.dot");
  val u1 = TextIO.output(outStream,"digraph{\nnodesep = 0.5;\nranksep = 0.35;\nnode [shape=plaintext];\n");
  val u2 = (Queue.app (fn node => TextIO.output(outStream, dotifyNode(node))) (!nodes)) 
  val u3 = TextIO.output(outStream, "subgraph dir\n{\n")
  val u4 = (Queue.app (fn edge => TextIO.output(outStream, dotifyEdge(edge))) tableauEdges) 
  val u5 = TextIO.output(outStream, "}\n");
  val u6 = TextIO.output(outStream, "subgraph undir\n{\n")
  val u7 = TextIO.output(outStream, "edge [dir=none, color=red]\n")
  val u8 = (Queue.app (fn edge => TextIO.output(outStream, dotifyEdge(edge))) conjEdges) 
  val u9 = TextIO.output(outStream, "}\n");
  val u10 = TextIO.output(outStream, "subgraph ancestor\n{\nedge [dir=back, color=blue, style=dashed]\n")
  val u12 = (Queue.app (fn edge => TextIO.output(outStream, dotifyEdge(edge))) unifyEdges) 
  val u13 = TextIO.output(outStream, "}\n}\n");
  val u14 = TextIO.closeOut outStream
  
  
  
end