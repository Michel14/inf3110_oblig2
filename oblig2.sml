datatype exp = Ident of string | Const of int | PlusExp of exp * (int * int -> int) * exp | BooleanExp of exp * (int * int -> bool) * exp; (* incomplete *)
datatype decl = Var of string * exp;
datatype direction = N | S | E | W;
datatype move = Forward | Backward | Left | Right;
datatype stmt = Start of exp*exp*direction
              | Stop
              (* Pen: *)
	      | PenUp | PenDown
              (* ... *)
              | Move of exp;
datatype grid = Size of int * int;
datatype robot = R of decl list * stmt list;
datatype p = P of grid * robot;

val p1 = [Stop];

val p2 = [Start (Const 0, Const 0, N), Stop];

val decls1 = [Var ("x", Const 5)
            ,Var ("y", Ident "x")
            ,Var ("z", Ident "a")];

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

datatype pen = Up | Down;
type position = int*int;
type board = unit; (* ... *)
type bindings = string -> int option;
datatype state = State of board * pen * position * direction * bindings;

fun eval binding (Const i) = i
  | eval binding _         = raise Fail "not implemented yet"; (* ... *)

(* Could use `fold` here *)
fun initialState nil acc = acc
  | initialState ((Var (v,e))::vs) (State (b,p,pos,dir,find)) = initialState vs (State (b,p,pos,dir, fn var => if (var = v) then SOME (eval (find) e)
                                                                                                                            else find var));

(* TODO: take direction into account *)
fun calculatePos (x,y) dir i = (x,y);

(* Step takes a state and a list of statements. Execute the first statement, and obtain an intermediate state.
   If we need to continue (i.e. not STOP), then use intermediate state to interpret remaining statements.
   Interpret runs the whole program. TODO: when and how do we stop?
*)
fun interpret (P (gr,R (decls,stmts))) = step (initialState decls (State ((), Up, (0,0), N, fn _ => NONE))) stmts
and step state (Stop::_) = state
  | step (State (b,p,pos,dir,bs)) (Move e::ss) = let val v = eval bs e
                                                     val s = State (b,p, calculatePos pos dir v, dir, bs)
                                              in step s ss end
  | step (State (b,_,pos,dir,bs)) (PenUp::ss) = step (State (b,Up,pos,dir,bs)) ss;


(* Example:

- interpret (P (nil,[Move (Const 1)]));

uncaught exception Match [nonexhaustive match failure]
  raised at: m.sml:67.82

*)
