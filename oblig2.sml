datatype exp = Ident of string | Const of int | PlusExp of exp * string * exp | BooleanExp of exp * string * exp; (* incomplete *)
datatype decl = Var of string * exp;
datatype direction = N | S | E | W;
(* datatype move = Forward | Backward  | Left  | Right ; *)
datatype stmt = Start of exp*exp*direction
              | Stop
              (* Pen: *)
              | PenUp | PenDown
              (* ... *)
	      (* | Forward of exp *)
	      (* | Backward of exp *)
	      (* | Left of exp *)
	      (* | Right of exp *)
              | Move of exp | Forward of exp | Backward of exp | Left of exp | Right of exp
              | Assignment of decl
	      | IfThenElse of exp * stmt list * stmt list
	      | While of exp * stmt list;
datatype grid = Size of int * int;
datatype robot = Rob of decl list * stmt list;
datatype program = Prog of grid * robot;

val whileStmt = [Forward (Const 1), Assignment (Var ("z", PlusExp(Ident "z", "-", Const 1)))];

val ifStmt = [Backward (Const 4)];
val elseStmt = [Forward (Const 4)];

val p1 = [Stop];

val p2 = [Start (Const 3, Const 9, N),
	  Forward (Const 3),
	  Backward (Const 7),
	  Left (Ident "z"),
	  Assignment (Var ("z", (Const 5))),
	  Forward (Ident "z"),
	  Right (PlusExp (Const 7, "-", Const 9)),
	  While (BooleanExp(Ident "z", ">", Const 0), whileStmt),
	  IfThenElse(BooleanExp(Const 1, "=", Const 2), ifStmt, elseStmt),
	  Stop];

val decls1 = [Var ("x", Const 10)
             ,Var ("y", Ident "x")
             ,Var ("z", Ident "y")];

(*
- val State (_,_,_,_,bs) = initialState decls1 (State ((), Up, (0,0), N, fn _ => NONE));
val bs = fn : bindings
- bs "x";
val it = SOME 5 : int option
- bs "y";

uncaught exception Fail [Fail: not implemented yet]
  raised at: m.sml:47.36-47.62
*)

(*
val p = [Start (Const 23, Const 30, S)
        ,Forward (Const 15)
        ,PenUp
        ,Left (Const 15)
        , Right (Add (Const 2) (Const 3))
        , PenDown
        , Backward (Add (Const 10) (Const 27))
        , Stop];
*)

(*
val pp = [Start (Const 23, Const 30, W)
        , Forward (Const 15)
        , PenDown
        , Left (Const 15)
        , Right (Add (Const 2) (Const 3))
        , PenUp
        , Backward (Add (Const 10) (Const 27))
        , Stop];
*)


datatype pen = Up | Down;
type position = int*int;
type board = unit; (* ... *)
type bindings = string -> int option;
datatype state = State of board * pen * position * direction * bindings;

exception Fail of string;

fun getTermOp "+" = op +
  | getTermOp "-" = op -
  | getTermOp "*" = op *
  | getTermOp _   = raise Fail "Unknown term operator";

fun getBoolOp ">" = op >
  | getBoolOp "<" = op <
  | getBoolOp "=" = op =
  | getBoolOp _   = raise Fail "Unknown bool operator";

fun eval binding (Const i) = i
  | eval binding (PlusExp (e1,s,e2)) = (getTermOp s)((eval binding e1), (eval binding e2))
  | eval binding (Ident s) = valOf (binding s)
  | eval binding _         = raise Fail "not implemented yet"; (* ... *)

(* Could use `fold` here *)
(* First argument is declarations, second is a initial state *)
fun initialState nil acc = acc
  | initialState ((Var (v,e))::vs) (State (b,p,pos,dir,find)) =
    initialState vs (State (b,p,pos,dir, fn var => if (var = v) then SOME (eval (find) e) else find var));

fun isTrueBoolean binding (BooleanExp (e1, opr, e2)) = (getBoolOp opr)((eval binding e1), (eval binding e2));

fun calculatePos (x,y) N i = (x,y+i)
  | calculatePos (x,y) S i = (x,y-i)
  | calculatePos (x,y) E i = (x+i,y)
  | calculatePos (x,y) W i = (x-i,y);

fun updatePos (Const x, Const y):position = (x,y);

fun expToString (Ident i) = i
  | expToString (Const c) = Int.toString c
  | expToString (PlusExp (e1, oper, e2)) = (expToString e1) ^ " " ^ oper ^ " " ^ (expToString e2)
  | expToString (BooleanExp (e1, oper, e2)) = (expToString e1) ^ " " ^ oper ^ " " ^ (expToString e2);

fun posToString (a, b) = ("(" ^ Int.toString a ^ ", " ^ Int.toString b ^ ")");

fun dirToString N = "y"
  | dirToString S = "-y"
  | dirToString E = "x"
  | dirToString W = "-x";

fun varToString (Var (str, e)):string = ("var " ^ str ^ " = " ^ (expToString e));

fun alterDir dir (Left e) = if dir = N then W else
			      if dir = W then S else
			      if dir = S then E else N
  | alterDir dir (Right e) = if dir = N then E else
			       if dir = E then S else
			       if dir = S then W else N
  | alterDir dir (Backward e) = if dir = N then S else
			       if dir = E then W else
			       if dir = W then E else N;

fun prettyPrint nil nil = nil
    | prettyPrint (d::ds) st                       = (print (varToString d ^ "\n"); prettyPrint ds st)
    | prettyPrint nil (Forward e::st)              = (print ("forward(" ^ expToString e ^ ")\n"); prettyPrint nil st)
    | prettyPrint nil (Backward e::st)             = (print ("backward(" ^ expToString e ^ ")\n"); prettyPrint nil st)
    | prettyPrint nil (Left e::st)                 = (print ("left(" ^ expToString e ^ ")\n"); prettyPrint nil st)
    | prettyPrint nil (Right e::st)                = (print ("right(" ^ expToString e ^ ")\n"); prettyPrint nil st)
    | prettyPrint nil (Start (e1, e2, newDir)::st) = (print ("start(" ^ expToString e1 ^ "," ^ expToString e2 ^ ", " ^ dirToString newDir ^ ")\n"); prettyPrint nil st)
    | prettyPrint nil (Assignment var::st)         = (print (varToString var ^ "\n"); prettyPrint nil st)
    | prettyPrint nil (While (e, stmtList)::st)    = (print ("while (" ^ expToString e  ^ ") {\n");
						      prettyPrint nil stmtList;
						      print "}\n"; prettyPrint nil st)
    | prettyPrint nil (IfThenElse (e, stmtList1, stmtList2)::st) =
                                                      (print ("if (" ^ expToString e  ^ ") {\n");
						       prettyPrint nil stmtList1;
						       if stmtList2 = nil then (print "}\n"; prettyPrint nil st)
						       else (print "} else {\n"; prettyPrint nil stmtList2; print "}\n"; prettyPrint nil st))
    | prettyPrint nil (Stop::st)                      = (print "Stop\n"; prettyPrint nil st);

(* Step takes a state and a list of statements. Execute the first statement, and obtain an intermediate state.
   If we need to continue (i.e. not STOP), then use intermediate state to interpret remaining statements.
   Interpret runs the whole program. TODO: when and how do we stop?
 *)
fun interpret (Prog (gr,Rob (decls,stmts))) = ((prettyPrint decls stmts); step (initialState decls (State ((), Up, (0,0), N, fn _ => NONE))) stmts)
and step state (Stop::_):state                  = state
  | step state nil = state
  | step (State (b,p,pos,dir,bs)) (Start (e1, e2, newDir)::ss) =
     let
	 val newPos = updatePos(e1,e2)
	 val s = State (b,p,newPos,newDir,bs)
     in
	 step s ss
     end

  | step (State (b,p,pos,dir,bs)) (Forward e::ss) = step (State (b,p,pos,dir,bs)) (Move e::ss)
  | step (State (b,p,pos,dir,bs)) (Backward e::ss) = step (State (b,p, pos, alterDir dir (Backward e),bs)) (Move e::ss)
  | step (State (b,p,pos,dir,bs)) (Left e::ss) = step (State (b,p, pos, (alterDir dir (Left e)),bs)) (Move e::ss)
  | step (State (b,p,pos,dir,bs)) (Right e::ss) = step (State (b,p, pos, (alterDir dir (Right e)),bs)) (Move e::ss)
  | step (State (b,p,pos,dir,bs)) (Move e::ss)  = let val v = eval bs e
                                                     val s = State (b,p, calculatePos pos dir v, dir, bs)
                                                 in step s ss end
  | step s (Assignment var::ss) = step (initialState [var] s) ss
  | step (State (b,p,pos,dir,bs)) (While (e, stmtList)::ss) =
    if
	(isTrueBoolean bs e)
    then
	step (step (State (b,p,pos,dir,bs)) stmtList) ((While (e, stmtList))::ss)
    else
	step (State (b,p,pos,dir,bs)) ss

  | step (State (b,p,pos,dir,bs)) (IfThenElse (e, stmtList1, stmtList2)::ss) =
    if
	(isTrueBoolean bs e)
    then
	step (step (State (b,p,pos,dir,bs)) stmtList1) ss
    else
	step (step (State (b,p,pos,dir,bs)) stmtList2) ss

  | step (State (b,_,pos,dir,bs)) (PenUp::ss)   = step (State (b,Up,pos,dir,bs)) ss
  | step (State (b,_,pos,dir,bs)) (PenDown::ss) = step (State (b,Down,pos,dir,bs)) ss;

(* Example:

- interpret (Prog (nil,[Move (Const 1)]));

uncaught exception Match [nonexhaustive match failure]
  raised at: m.sml:67.82

 *)

interpret (Prog (Size (12,12), Rob (decls1, p2)));
