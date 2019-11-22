////////// Definitions //////////
// L1 definition
type Ident = string
type Bool = bool
type Int = int
// Uncomment each command and add the TypeInfer implementation
datatype Exp    = NVAL(n: Int)
                | BVAL(b: Bool)
                // // Algebric
                // | SUM(e1: Exp, e2: Exp) | MINUS(e1: Exp, e2: Exp) 
                // | MULT(e1: Exp, e2: Exp) | DIV(e1: Exp, e2: Exp) 
                // // Logic
                // | EQ(e1: Exp, e2: Exp) | DIF(e1: Exp, e2: Exp) 
                // | LT(e1: Exp, e2: Exp) | LE(e1: Exp, e2: Exp)
                // | GT(e1: Exp, e2: Exp) | GE(e1: Exp, e2: Exp)
                // | AND(e1: Exp, e2: Exp) | OR(e1: Exp, e2: Exp)
                // | NOT(e: Exp)
                // // Pair
                // | PAIR(e1: Exp, e2: Exp) | FST(e: Exp) | SND(e: Exp)
                // | IF(e1: Exp, e2: Exp, e3: Exp)
                // | ID(x: Ident)
                // | APP(e1: Exp, e2: Exp)
                // | FN(x: Ident, e: Exp)
                // | LET(x: Ident, e1: Exp, e2: Exp)
                // | LETREC(f: Ident, y: Exp, e1: Exp, e2: Exp) // FIXME
                // | NIL | CONS(e1: Exp, e2: Exp) | HD(e: Exp) | TL(e: Exp)
                // | RAISE | TRY(e1: Exp, e2: Exp)

// Types definition
datatype List<T> = Nil | Cons(head: T, tail: List<T>)
datatype T = X | Int | Bool | Fun(input: T, output: T) | List | Pair(0: T, 1: T)

////////// Type infer logic //////////
datatype IdentTypePair = identTypePair(0: Ident, 1: T)
datatype Env = env(map<Exp, T>)
// Type equations Cons((X, Bool), Cons((Y, Int), Empty)) (good for pattern match)
datatype TypeEq = Empty | Cons(head: IdentTypePair, tail: TypeEq) 

method Main() {
  print "hello, Dafny\n";
  var env := env(map[]);
  var p := Exp.NVAL(5);
  var ret := typeInfer(env, p);
  print(ret);
}

method typeInfer(env: Env, P: Exp) returns (typeInfered: T) {
  var t, c := collect(env, P);
  var sigma := unify(c);
  // applysubs(σ, t);
  return t;
}

method collect(env: Env, e: Exp) returns (t: T, eq: TypeEq) {
  // (T.Int, typeEq({identTypePair("X", T.Int)}))
  match e {
    case NVAL(n) => { t := T.Int; eq := Empty; }
    case BVAL(b) => { t := T.Bool; eq := Empty; }
  }
}

method unify(eq: TypeEq) returns (ret: TypeEq) {
  match eq {
    case Empty => ret := Empty;
    case Cons(head, tail) => ret := tail;
  }
}