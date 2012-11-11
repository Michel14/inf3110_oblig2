datatype exp = Ident of string | Const of int | PlusExp of exp * string * exp | BooleanExp of exp * string * exp;
datatype decl = Var of string * exp;
datatype direction = N | S | E | W;

datatype stmt = Start of exp*exp*direction
              | Stop
              (* Pen: *)
              | PenUp | PenDown
              | Move of exp
	      | Forward of exp | Backward of exp | Left of exp | Right of exp
              | Assignment of decl
	      | IfThenElse of exp * stmt list * stmt list
	      | While of exp * stmt list;
datatype grid = Size of int * int;
datatype robot = Rob of decl list * stmt list;
datatype program = Prog of grid * robot;

datatype pen = Up | Down;
type position = int*int;
type board = string list;
(* Bindings is functions to functions holding all variables and corresponding value *)
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

(* Finds value expression *)
fun eval binding (Const i):int = i
  | eval binding (PlusExp (e1,s,e2)) = (getTermOp s)((eval binding e1), (eval binding e2))
  | eval binding (Ident s) = valOf (binding s);

(* Could use `fold` here *)
(* First argument is declarations, second is a initial state *)
fun initialState nil acc = acc
  | initialState ((Var (v,e))::vs) (State (b,p,pos,dir,find)) =
    initialState vs (State (b,p,pos,dir, fn var => if (var = v) then SOME (eval (find) e) else find var));

(* Checks if a boolean expression is true *)
fun isTrueBoolean binding (BooleanExp (e1, opr, e2)) = (getBoolOp opr)((eval binding e1), (eval binding e2));

(* Calculate new position *)
fun calculatePos (x,y) N i = (x,y+i)
  | calculatePos (x,y) S i = (x,y-i)
  | calculatePos (x,y) E i = (x+i,y)
  | calculatePos (x,y) W i = (x-i,y);

(** TO-STRING FUNCTIONS - return string from different types of statements **)
  fun expToString (Ident i) = i
    | expToString (Const c) = Int.toString c
    | expToString (PlusExp (e1, oper, e2)) = (expToString e1) ^ " " ^ oper ^ " " ^ (expToString e2)
    | expToString (BooleanExp (e1, oper, e2)) = (expToString e1) ^ " " ^ oper ^ " " ^ (expToString e2);

  fun posToString (a, b) = ("(" ^ Int.toString a ^ ", " ^ Int.toString b ^ ")");

  fun dirToString N = "y"
    | dirToString S = "-y"
    | dirToString E = "x"
    | dirToString W = "-x";

  fun dirToChar N = #"^"
    | dirToChar S = #"v"
    | dirToChar E = #">"
    | dirToChar W = #"<";

  fun varToString (Var (str, e)):string = ("var " ^ str ^ " = " ^ (expToString e));

(* Finds the new direction according to which way the robot is about to go *)
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
						       else (print "} else {\n"; prettyPrint nil stmtList2;
							     print "}\n"; prettyPrint nil st))
    | prettyPrint nil (PenUp::st)                  = (print "up\n"; prettyPrint nil st)
    | prettyPrint nil (PenDown::st)                = (print "down\n"; prettyPrint nil st)
    | prettyPrint nil (Stop::st)                   = (print "stop\n"; prettyPrint nil st);


(* Returns (x,y) if they are inside grid, raises exception if not *)
fun insideGrid (b::bs) (x,y) = if x <= (size b) andalso x > 0 andalso
				  y <= (length (b::bs)) andalso y > 0
			       then (x,y)
			       (* else (print ("Outside grid: (" ^ (Int.toString x) ^ "," ^ (Int.toString y) ^ ")\n"); raise Fail ("Outside grid: (" ^ (Int.toString x) ^ "," ^ (Int.toString y) ^ ")\n")); *)
			       else
				   (print ("\nERROR: outside grid (" ^ (Int.toString x) ^ "," ^ (Int.toString y) ^ ")\n"); raise Fail "");

(* handle Fail s => (print s; OS.Process.exit); *)

fun makeColumns (0,col:string):string = col
  | makeColumns (x,col:string):string = makeColumns(x-1,(col ^ "."));

fun makeBoard (Size (x,0)) lst = lst
  | makeBoard (Size (x,y)) lst = makeBoard (Size (x,y-1)) ((makeColumns(x,""))::lst);

(* Prints one row in a board *)
fun printRow nil = nil
  | printRow (b::bs) = (print (Char.toString b ^ " "); printRow bs);

(* Prints whole board *)
fun printBoard nil = nil
    | printBoard (b::bs) = (printRow (explode b); print "\n"; printBoard bs);

fun printPos (x,y) dir = print ("Position is now: (" ^ Int.toString x ^ ", " ^ Int.toString y ^ ") " ^ dirToString dir ^ "\n\n");

(* Sets position in board with symbol "sym" at position (x,y) *)
fun setPosInBoard (x,y) (b::bs) sym =
    let
	val yLength = (length (b::bs))
	val xLength = size b

	(* Since retval from setX is a char list, I have to use implode to get the string value
	 (and since setX expects char list, I have to use explode on the string "b") *)
	fun setY (x,0) (b::bs) = ((implode (setX x (explode b)))::bs)
	  | setY (x,y) (b::bs) = (b::(setY (x,y-1) bs)) and
  	setX 0 (b::bs) = (sym::bs) (* Sets the symbol here *)
	| setX x (b::bs) = (b::(setX (x-1) bs))
    in
	setY (x-1, yLength - y) (b::bs)
    end;

(* Updates the board, where (x,y) is the new position, and (xO,yO) is the old) *)
fun penDown (x,y) (xO, yO) b sym =
    let
	val xC = (x-xO)
	val yC = (y-yO)

	(* Recursive function for setting positions when going either backwards or downwards *)
	fun penDNegative (0,0) br = br
	  | penDNegative (0, yC) br = penDNegative (0, yC+1) (setPosInBoard (x, (y-yC)-1) br sym)
	  | penDNegative (xC, 0) br = penDNegative (xC+1, 0) (setPosInBoard ((x-xC)-1, y) br sym)

	(* Recursive function for setting positions when going either forwards or upwards *)
	fun penDPositive (0, 0) br = br
	  | penDPositive (0, yC) br = penDPositive (0, yC-1) (setPosInBoard (x, yO+yC) br sym)
	  | penDPositive (xC, 0) br = penDPositive (xC-1, 0) (setPosInBoard (xO+xC, y) br sym)
    in
	if xC < 0 orelse yC < 0 then penDNegative (xC, yC) b else penDPositive (xC, yC) b
    end;

(* Step takes a state and a list of statements. Execute the first statement, and obtain an intermediate state.
   If we need to continue (i.e. not STOP), then use intermediate state to interpret remaining statements.
   Interpret runs the whole program. TODO: when and how do we stop?
 *)
fun interpret (Prog (gr,Rob (decls,stmts))) = ((prettyPrint decls stmts); step (initialState decls (State ((makeBoard gr nil), Up, (0,0), N, fn _ => NONE))) stmts)
and step (State (b,p,pos,dir,bs)) (Stop::_):state              = (printBoard b; printPos pos dir; (State (b,p,pos,dir,bs)))

  (* Base case used in "while loop" *)
  | step state nil = state

  (* Start *)
  (* | step (State (b,p,pos,dir,bs)) (Start (Const x, Const y, newDir)::ss) = step (State ((updateBoard pos (0,0) b),p,(x, y),newDir,bs)) ss *)
  | step (State (b,p,pos,dir,bs)) (Start (Const x, Const y, newDir)::ss) =
    step (State ((setPosInBoard (x,y) b (dirToChar newDir)),p,(x, y),newDir,bs)) ss

  (* Forward *)
  | step (State (b,p,pos,dir,bs)) (Forward e::ss) = step (State (b,p,pos,dir,bs)) (Move e::ss)

  (* Backward *)
  | step (State (b,p,pos,dir,bs)) (Backward e::ss) = step (State (b,p, pos, alterDir dir (Backward e),bs)) (Move e::ss)

  (* Left *)
  | step (State (b,p,pos,dir,bs)) (Left e::ss) = step (State (b,p, pos, (alterDir dir (Left e)),bs)) (Move e::ss)

  (* Right *)
  | step (State (b,p,pos,dir,bs)) (Right e::ss) = step (State (b,p, pos, (alterDir dir (Right e)),bs)) (Move e::ss)

  (* Move *)
  | step (State (b,p,pos,dir,bs)) (Move e::ss)  = let val v = eval bs e
						      val newPos = calculatePos pos dir v
                                                  in
						      if p = Down then step (State ((penDown newPos pos b (dirToChar dir)),p, (insideGrid b newPos), dir, bs)) ss
						      else step (State (b,p, (insideGrid b newPos), dir, bs)) ss
						  end

  (* Assignment *)
  | step s (Assignment var::ss) = step (initialState [var] s) ss

  (* While loop *)
  | step (State (b,p,pos,dir,bs)) (While (e, stmtList)::ss) =
    if
	(isTrueBoolean bs e)
    then
	(* Calls step again, with updated state *)
	step (step (State (b,p,pos,dir,bs)) stmtList) ((While (e, stmtList))::ss)
    else
	step (State (b,p,pos,dir,bs)) ss

  (* IfThenElse  *)
  | step (State (b,p,pos,dir,bs)) (IfThenElse (e, stmtList1, stmtList2)::ss) =
    if
	(isTrueBoolean bs e)
    then
	step (step (State (b,p,pos,dir,bs)) stmtList1) ss
    else
	step (step (State (b,p,pos,dir,bs)) stmtList2) ss

  | step (State (b,_,pos,dir,bs)) (PenUp::ss)   = step (State (b,Up,pos,dir,bs)) ss
  | step (State (b,_,pos,dir,bs)) (PenDown::ss) = step (State (b,Down,pos,dir,bs)) ss;


(* ############ *)
(* RUN EXAMPLES *)

(* ### EXAMPLE GRID ### *)

val exampleGrid = [PenDown,
		   Start (Const 2, Const 3, E),
		   Forward (Const 3),
		   Left (Const 4),
		   Backward (Const 1),
		   Right (Const 2),
		   Stop];

(* interpret (Prog (Size (9,7), Rob ([], exampleGrid))); *)

(* ### TESTING CODE 1 ### *)

val code1 = [Start (Const 23, Const 30, W)
            , Forward (Const 15)
            , PenDown
            , Left (Const 15)
            , Right (PlusExp ((Const 2), "+", (Const 3)))
            , PenUp
            , Backward (PlusExp ((Const 10), "+", (Const 27)))
            , Stop];

(* interpret (Prog (Size (64,64), Rob ([], code1))); *)


(* ### TESTING CODE 2 ### *)

val code2decls = [Var ("i", Const 5),
		  Var ("j", Const 3)]

val code2 = [Start (Const 23, Const 6, W),
             PenDown, (* Added *)
             Forward (PlusExp(Const 3, "*", Ident "i")),
             PenDown,
             Right (Const 15),
             Left (Const 4),
	     (* PenUp, *)
	     Backward (PlusExp(
			    PlusExp (
				(PlusExp (Const 2, "*", Ident "i")),
				"+",
				(PlusExp (Const 3, "*", Ident "j"))),
			    "+",
			    Const 5)),
	     Stop];



(* interpret (Prog (Size (64,64), Rob (code2decls, code2))); *)


(* ### TESTING CODE 4 ### *)

val code4decls = [Var ("i", Const 5),
		  Var ("j", Const 3)]

val code4whileStmt = [Right (Ident "j"), Assignment (Var ("j", PlusExp(Ident "j", "-", Const 1)))];

val code4ifStmt = [Forward (Const 14)];
val code4elseStmt = [Backward (Const 14)];

val code4 = [Start (Const 23, Const 6, W),
             PenDown, (* Added *)
             Forward (PlusExp(Const 3, "*", Ident "i")),
             PenDown,
             Right (Const 15),
             Left (Const 4),
	     (* PenUp, *)
	     Backward (PlusExp(
			    PlusExp (
				(PlusExp (Const 2, "*", Ident "i")),
				"+",
				(PlusExp (Const 3, "*", Ident "j"))),
			    "+",
			    Const 5)),
	     While (BooleanExp(Ident "j", ">", Const 0), code4whileStmt),
	     IfThenElse(BooleanExp(Ident "i", ">", Const 3), code4ifStmt, code4elseStmt),
	     Stop];

interpret (Prog (Size (64,64), Rob (code4decls, code4)));
