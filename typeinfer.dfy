////////// LI Definitions //////////
type Ident = string
type Bool = bool
type Int = int
// Uncomment each command and add the TypeInfer implementation
datatype Bop = SUM | MINUS | MULT | DIV                // Algebric
             | EQ | NEQ | LT | LE | GT | GE | AND | OR // Binary Logic
datatype Uop = NOT                                     // Unary Logic
// L1 Abstract Syntactic Tree
datatype Exp    = NVAL(n: Int)
                | BVAL(b: Bool)
                | BINOP(bop: Bop, e1: Exp, e2: Exp) 
                | UNOP(uop: Uop, e: Exp)
                | PAIR(e1: Exp, e2: Exp) | FST(e: Exp) | SND(e: Exp)
                | IF(e1: Exp, e2: Exp, e3: Exp)
                | ID(x: Ident)
                | APP(e1: Exp, e2: Exp) // e1 function and e2 value
                | FN(x: Ident, e: Exp)
                | LET(x: Ident, e1: Exp, e2: Exp)
                | LETREC(f: Ident, y: Ident, e1: Exp, e2: Exp)
                | NIL | CONS(e1: Exp, e2: Exp) | HD(e: Exp) | TL(e: Exp) | ISEMPTY(e: Exp)
                | RAISE | TRY(e1: Exp, e2: Exp)

// Types definition
datatype T = X(n: int) | Int | Bool | Fun(input: T, output: T) | List(t: T) | Pair(0: T, 1: T) | UNDEFINED

//////////////////////////////////////
////////// Type infer logic //////////
datatype TypePair = typePair(a: T, b: T)
type TypeEq = set<TypePair> 
type Env = map<Ident, T>

class TypeInfer {
  var variables: int;

  method typeInfer(env: Env, P: Exp) returns (typeInfered: T) 
    modifies this // to update the variables
    decreases *
  {
    this.variables := 0;
    var t, c := collect(env, P); print("\n");
    var sigma, success := unify({}, c);
    
    print("Sigma: "); print(sigma); print("\n");
    if (success) {
      return t;
    } else {
      return T.UNDEFINED;
    } 
    // applysubs(σ, t);
  }

  method collect(env: Env, e: Exp) returns (t: T, eq: TypeEq)
    modifies this // to update the variables
    decreases *
    ensures |env| >= 0
  {
    var newEnv: Env := env;
    match e {
      case NVAL(n) => t := T.Int; eq := {}; print("Collect NVAL ");
      case BVAL(b) => t := T.Bool; eq := {}; print("Collect BVAL ");
      case BINOP(bop: Bop, e1: Exp, e2: Exp) => {
        var t1, c1 := collect(env, e1);
        var t2, c2 := collect(env, e2); 
        var newTypeEq : TypeEq;
        if {
          case bop == SUM || bop == MINUS || bop == MULT || bop == DIV => 
            newTypeEq := {typePair(t1, T.Int), typePair(t2, T.Int)};
            t := t2; eq := c1 + c2 + newTypeEq; print("Collect BINOP - INT INT => INT ");
          case bop == EQ || bop == NEQ || bop == LT || bop == LE || bop == GT || bop == GE => 
            newTypeEq := {typePair(t1, T.Int), typePair(t2, T.Int)};
            t := T.Bool; eq := c1 + c2 + newTypeEq; print("Collect BINOP - INT INT => BOOL ");
          case bop == bop == AND || bop == OR => 
            newTypeEq := {typePair(t1, T.Bool), typePair(t2, T.Bool)};
            t := t2; eq := c1 + c2 + newTypeEq; print("Collect BINOP - BOOL BOOL => BOOL ");
        }
      }
      case UNOP(uop: Uop, e1: Exp) => {
        var t1, c1 := collect(env, e1);
        var newTypeEq := {typePair(t1, T.Bool)};
        t := t1; eq := c1 + newTypeEq; print("Collect UNOP ");
      }
      case IF(e1: Exp, e2: Exp, e3: Exp) => {
        var t1, c1 := collect(env, e1);
        var t2, c2 := collect(env, e2); 
        var t3, c3 := collect(env, e3); 
        var newTypeEq := {typePair(t1, T.Bool), typePair(t2, t3)};
        t := t2; eq := c1 + c2 + c3 + newTypeEq; print("Collect IF ");
      }
      case PAIR(e1: Exp, e2: Exp) => {
        var t1, c1 := collect(env, e1);
        var t2, c2 := collect(env, e2); 
        t := T.Pair(t1, t2); eq := c1 + c2; print("Collect PAIR ");
      }
      case FST(e1: Exp) => {
        var pairType, c1 := collect(env, e1); print("Collect FST ");
        match pairType {
          case Pair(t1: T, t2: T) => t := t1; eq := c1;
          case Bool => t:= UNDEFINED; eq := {};
          case Int => t:= UNDEFINED; eq := {};
          case List(tlist: T) => t:= UNDEFINED; eq := {};
          case X(n: int) => t:= UNDEFINED; eq := {};
          case Fun(input: T, output: T) => t:= UNDEFINED; eq := {};
          case UNDEFINED => t:= UNDEFINED; eq := {};
        }
      }
      case SND(e1: Exp) => {
        var pairType, c1 := collect(env, e1); print("Collect SND ");
        match pairType {
          case Pair(t1: T, t2: T) => t := t2; eq := c1;
          case Bool => t:= UNDEFINED; eq := {};
          case Int => t:= UNDEFINED; eq := {};
          case List(tlist: T) => t:= UNDEFINED; eq := {};
          case X(n: int) => t:= UNDEFINED; eq := {};
          case Fun(input: T, output: T) => t:= UNDEFINED; eq := {};
          case UNDEFINED => t:= UNDEFINED; eq := {};
        }
      }
      case ID(x: Ident) => {
        if (x in env) {
          t := env[x]; eq := {}; print("Collect ID ");
        } else {
          print("ERROR: Ident not found in the envelopment\n");
        }
      }
      case NIL => {
        this.variables := this.variables + 1; var X := T.X(this.variables); // X new
        t := T.List(X); eq := {}; print("Collect NIL ");
      } 
      case CONS(e1: Exp, e2: Exp) => {
        var t1, c1 := collect(env, e1);
        var t2, c2 := collect(env, e2);
        var newTypeEq := {typePair(List(t1), t2)};
        t := t2; eq := c1 + c2 + newTypeEq; print("Collect CONS ");
      }
      case HD(e1: Exp) => {
        var t1, c1 := collect(env, e1);
        this.variables := this.variables + 1; var X := T.X(this.variables); // X new
        var newTypeEq := {typePair(t1, List(X))};
        t := X; eq := c1 + newTypeEq; print("Collect HD ");
      }
      case TL(e1: Exp) => {
        var t1, c1 := collect(env, e1);
        this.variables := this.variables + 1; var X := T.X(this.variables); // X new
        var newTypeEq := {typePair(t1, List(X))};
        t := X; eq := c1 + newTypeEq; print("Collect TL ");
      }
      case ISEMPTY(e1: Exp) => {
        var t1, c1 := collect(env, e1);
        this.variables := this.variables + 1; var X := T.X(this.variables); // X new
        var newTypeEq := {typePair(t1, List(X))};
        t := T.Bool; eq := c1 + newTypeEq; print("Collect ISEMPTY ");
      }
      case RAISE => {
        this.variables := this.variables + 1; var X := T.X(this.variables); // X new
        t := X; eq := {}; print("Collect RAISE ");
      }
      case TRY(e1: Exp, e2: Exp) => {
        var t1, c1 := collect(env, e1);
        var t2, c2 := collect(env, e2);
        var newTypeEq := {typePair(t1, t2)};
        t := t2; eq := c1 + c2 + newTypeEq; print("Collect TRY ");
      }
      case APP(e1: Exp, e2: Exp) => {
        var t1, c1 := collect(env, e1);
        var t2, c2 := collect(env, e2);
        this.variables := this.variables + 1; var X := T.X(this.variables); // X new
        var newTypeEq := {typePair(t1, T.Fun(t2, X))};
        t := X; eq := c1 + c2 + newTypeEq; print("Collect APP ");
      }
      case FN(x: Ident, e1: Exp) => {
        this.variables := this.variables + 1; var X := T.X(this.variables); // X new
        newEnv := newEnv[x := X];
        var t1, c1 := collect(newEnv, e1);
        t := T.Fun(X, t1); eq := c1; print("Collect FN ");
      }
      case LET(x: Ident, e1: Exp, e2: Exp) => {
        var t1, c1 := collect(env, e1);
        this.variables := this.variables + 1; var X := T.X(this.variables); // X new
        newEnv := newEnv[x := X];
        var t2, c2 := collect(newEnv, e2);
        var newTypeEq := {typePair(X, t1)};
        t := t2; eq := c1 + c2 + newTypeEq; print("Collect LET ");
      }
      case LETREC(f: Ident, y: Ident, e1: Exp, e2: Exp) => {
        this.variables := this.variables + 1; var X := T.X(this.variables); // X new
        this.variables := this.variables + 1; var Y := T.X(this.variables); // Y new
        newEnv := newEnv[f := X];
        var envWithoutY := newEnv;
        newEnv := newEnv[y := Y];
        var t1, c1 := collect(newEnv, e1);
        var t2, c2 := collect(envWithoutY, e2);
        var newTypeEq := {typePair(X, T.Fun(Y, t1))};
        t := t2; eq := c1 + c2 + newTypeEq; print("Collect LETREC ");
      }
    }
    // print(eq); print("\n");
  }

  method unify(sigma: TypeEq, eq: TypeEq) returns (sigmaRet: TypeEq, success: bool)  
    modifies this
    decreases *
  {
    sigmaRet := sigma;
    success := true;
    var mutableEq := eq;
    // print("Received equation: "); print(eq); print("\n");

    if (eq != {}) {
      var pairType: TypePair :| pairType in eq;
      mutableEq := mutableEq - {pairType}; // remove current pair type
      match pairType {
        case typePair(a: T, b: T) => {
          match a {
            case X(n1: int) => {
              match b {
                case X(n2: int) => {
                  sigmaRet, success := unify(sigmaRet, mutableEq);
                  return;
                }
                case Fun(t1: T, t2: T) => case Pair(t3: T, t4: T) => case List(t2list: T) => case Bool => case Int => case UNDEFINED =>
              }
              var linkedVariable := TFind(b, n1);
              if (linkedVariable) {
                success := false;
                return;
              }
              sigmaRet := sigma + {typePair(X(n1), b)};
              var eqChanger := typeEqChange(eq, X(n1), b);
              mutableEq := mutableEq + eqChanger;
              sigmaRet, success := unify(sigmaRet, mutableEq);
              return;
            }
            case Fun(t1: T, t2: T) => {
              match b {
                case Fun(t3: T, t4: T) => {
                  mutableEq := mutableEq + {typePair(t1, t3)} + {typePair(t2, t4)};
                  sigmaRet, success := unify(sigmaRet, mutableEq);
                  return;
                }
                case Pair(t3: T, t4: T) => case List(t2list: T) => case X(n: int) => case Bool => case Int => case UNDEFINED =>
              }
            }
            case Pair(t1: T, t2: T) => {
              match b {
                case Pair(t3: T, t4: T) => {
                  mutableEq := mutableEq + {typePair(t1, t3)} + {typePair(t2, t4)};
                  sigmaRet, success := unify(sigmaRet, mutableEq);
                  return;
                }
                case Fun(t3: T, t4: T) => case List(t2list: T) => case X(n: int) => case Bool => case Int => case UNDEFINED =>
              }
            }
            case List(t1list: T) => {
              match b {
                case List(t2list: T) => {
                  mutableEq := mutableEq + {typePair(t1list, t2list)};
                  sigmaRet, success := unify(sigmaRet, mutableEq);
                  return;
                }
                case Pair(t3: T, t4: T) => case Fun(t3: T, t4: T) => case X(n: int) => case Bool => case Int => case UNDEFINED =>
              }
            }
            case Bool => {
              if (b == Bool) {
                sigmaRet, success := unify(sigmaRet, mutableEq);
                return;
              }
            }
            case Int => {
              if (b == Int) {
                sigmaRet, success := unify(sigmaRet, mutableEq);
                return;
              }
            }
            case UNDEFINED =>
          }
          match b {
            case X(n: int) => {
              var linkedVariable := TFind(a, n);
              if (linkedVariable) {
                success := false;
                return;
              }
              sigmaRet := sigma + {typePair(X(n), a)};
              var eqChanger := typeEqChange(eq, X(n), a);
              mutableEq := mutableEq + eqChanger;
              sigmaRet, success := unify(sigmaRet, mutableEq);
              return;
            }
            // All others tests in match "a"
            case Fun(t1: T, t2: T) => case Pair(t1: T, t2: T) => case List(tlist: T) => case Bool => case Int => case UNDEFINED =>
          }
        }
      }
    } else {
      return; // all equations processed
    }
    success := false; // não passou por nenhum "return" na sessão de match
  }
}

// caminha na árvore de tipos T, retornando true se achou X(n) ou falso caso contrário
method TFind(tree: T, x_index: int) returns (ret: bool)
  decreases *
{
  ret := false;
  match (tree) {
    case X(n: int) =>
      ret := n == x_index;
    case Fun(t1: T, t2: T) => {
      var x1Node := TFind(t1, x_index);
      var x2Node := TFind(t2, x_index);
      ret := x1Node || x2Node;
    }
    case Pair(t1: T, t2: T) => {
      var x1Node := TFind(t1, x_index);
      var x2Node := TFind(t2, x_index);
      ret := x1Node || x2Node;
    }
    case List(tlist: T) => {
      var tlistNode := TFind(tlist, x_index);
      ret := tlistNode;
    }
    case Bool => case Int => case UNDEFINED =>
  }
}

// caminha na árvore de tipos T, substituindo o tipo "from" por "to"
method TChange(tree: T, from: T, to: T) returns (ret: T)
  decreases *
{
  if (tree == from) {
    ret := to;
  } else {
    ret := tree; // don't substitute
    match (tree) {
      case Fun(t1: T, t2: T) => {
        var t1Node := TChange(t1, from, to);
        var t2Node := TChange(t2, from, to);
        ret := Fun(t1Node, t2Node);
      }
      case Pair(t1: T, t2: T) => {
        var t1Node := TChange(t1, from, to);
        var t2Node := TChange(t2, from, to);
        ret := Fun(t1Node, t2Node);
      }
      case List(tlist: T) => {
        var tlistNode := TChange(tlist, from, to);
        ret := List(tlistNode);
      }
      case Bool => case Int => case X(n: int) => case UNDEFINED =>
    }
  }
}

method typeEqChange(eq: TypeEq, from: T, to: T) returns (changed: TypeEq)
  decreases *
{
  // print("====== typeEqChange ======\n");
  // print("Equation: "); print(eq); print("\n");
  // print("From: "); print(from); print("\n");
  // print("To: "); print(to); print("\n");
  changed := {};
  var it := eq;
  while (it != {})
    decreases * 
  {
    var pairType: TypePair :| pairType in it;
    var treeChangedLeft := TChange(pairType.a, from, to);
    var treeChangedRight := TChange(pairType.b, from, to);
    changed := changed + {typePair(treeChangedLeft, treeChangedRight)};
    it := it - {pairType};
  }
  // print("Changed: "); print(changed); print("\n");
}

// 
method Main()
 decreases *
 {
  var typeInfer := new TypeInfer;
  var env := map[];
  var typeInfered: T;

  ///////////// Tests /////////////
  print("===> BOP FAIL\n");
  typeInfered := typeInfer.typeInfer(env, Exp.BINOP(Bop.SUM, Exp.NVAL(5), Exp.BVAL(true)));
  print("======== "); print(typeInfered); print(" == T.UNDEFINED ======== \n");

  print("===> BOP SUCCESS\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.BINOP(
      Bop.MULT,
      Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)), 
      Exp.BINOP(Bop.SUM, Exp.NVAL(5), Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)))
    )
  );
  print("======== "); print(typeInfered); print(" == T.Int ======== \n");

  print("===> UOP FAIL\n");
  typeInfered := typeInfer.typeInfer(env, Exp.UNOP(Uop.NOT, Exp.BINOP(Bop.SUM, Exp.NVAL(5), Exp.NVAL(4))));
  print("======== "); print(typeInfered); print(" == T.UNDEFINED ======== \n");

  print("===> UOP SUCCESS\n");
  typeInfered := typeInfer.typeInfer(env, Exp.UNOP(Uop.NOT, Exp.BVAL(true)));
  print("======== "); print(typeInfered); print(" == T.Bool ======== \n");

  print("===> IF FAIL 1\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.IF(
      Exp.UNOP(Uop.NOT, Exp.BVAL(true)), // T.Bool
      Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)), // T.Int
      Exp.BINOP(Bop.LT, Exp.BVAL(true), Exp.BVAL(false)) // T.Bool
    )
  );
  print("======== "); print(typeInfered); print(" == T.UNDEFINED ======== \n");

  print("===> IF FAIL 2\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.IF(
      Exp.UNOP(Uop.NOT, Exp.BVAL(true)), // T.Bool
      Exp.BINOP(Bop.LT, Exp.BVAL(true), Exp.BVAL(false)), // T.Bool
      Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)) // T.Int
    )
  );
  print("======== "); print(typeInfered); print(" == T.UNDEFINED ======== \n");

  print("===> IF FAIL 3\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.IF(
      Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), // T.Int
      Exp.NVAL(8), // T.Int
      Exp.NVAL(8)  // T.Int
    )
  );
  print("======== "); print(typeInfered); print(" == T.UNDEFINED ======== \n");

  print("===> IF SUCCESS\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.IF(
      Exp.UNOP(Uop.NOT, Exp.BVAL(true)), // T.Bool
      Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)), // T.Int
      Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8))  // T.Int
    )
  );
  print("======== "); print(typeInfered); print(" == T.Int ======== \n");

  print("===> PAIR FAIL 1\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.FST(
      Exp.BINOP(Bop.LT, Exp.BVAL(true), Exp.BVAL(false))
    )
  );
  print("======== "); print(typeInfered); print(" == T.UNDEFINED ======== \n");

  print("===> PAIR FAIL 2\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.FST(
      Exp.BINOP(Bop.LT, Exp.BVAL(true), Exp.BVAL(false))
    )
  );
  print("======== "); print(typeInfered); print(" == T.UNDEFINED ======== \n");

  print("===> FST PAIR SUCCESS\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.FST(
      Exp.PAIR(
        Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)), 
        Exp.BINOP(Bop.LT, Exp.NVAL(8), Exp.NVAL(3))
      )
    )
  );
  print("======== "); print(typeInfered); print(" == T.Int ======== \n");

  print("===> SND PAIR SUCCESS\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.SND(
      Exp.PAIR(
        Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)), 
        Exp.BINOP(Bop.LT, Exp.NVAL(8), Exp.NVAL(3))
      )
    )
  );
  print("======== "); print(typeInfered); print(" == T.Bool ======== \n");

  print("===> TRY FAIL\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.TRY(
      Exp.PAIR(
        Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)), 
        Exp.BINOP(Bop.LT, Exp.BVAL(true), Exp.BVAL(false))
      ), // T.Int x T.Bool
      Exp.IF( 
        Exp.UNOP(Uop.NOT, Exp.BVAL(true)), // T.Bool
        Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)), // T.Int
        Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8))  // T.Int
      ) // T.Int
    )
  );
  print("======== "); print(typeInfered); print(" == T.UNDEFINED ======== \n");

  print("===> TRY SUCCESS\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.SND(
      Exp.TRY(
        Exp.PAIR(Exp.NVAL(8), Exp.NVAL(8)), // T.Int x T.Int
        Exp.PAIR(Exp.NVAL(8), Exp.NVAL(8))  // T.Int x T.Int
      )
    )
  );
  print("======== "); print(typeInfered); print(" == T.Int ======== \n");

  print("===> FUNCTION FAIL\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.APP(
      Exp.PAIR(Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)),
      Exp.NVAL(5)
    )
  );
  print("======== "); print(typeInfered); print(" == T.UNDEFINED ======== \n");

  print("===> FUNCTION SUCCESS\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.APP(
      Exp.FN(
        "r", 
        Exp.BINOP(Bop.MINUS, Exp.ID("r"), Exp.NVAL(8)) 
      ),
      Exp.NVAL(5)
    )
  );
  print("======== "); print(typeInfered); print(" == T.X (Int) ======== \n");

  print("===> LET SUCCESS\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.LET(
      "y",
      Exp.BINOP(Bop.MINUS, Exp.NVAL(10), Exp.NVAL(5)), // y = Int (5)
      Exp.LET(
        "x",
        Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(4)), // x = Int (1)
        Exp.BINOP(Bop.SUM, Exp.ID("x"), Exp.ID("y")) // x + y = Int
      )
    )
  );
  print("======== "); print(typeInfered); print(" == T.X (Int) ======== \n");
  
  print("===> LET SUCCESS\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.LET(
      "y",
      Exp.BVAL(true), // y = Bool
      Exp.IF(
        Exp.ID("y"), 
        Exp.NVAL(1), 
        Exp.NVAL(0)
      )
    )
  );
  print("======== "); print(typeInfered); print(" == T.Int ======== \n");

  print("===> LET FAIL\n");
  typeInfered := typeInfer.typeInfer(env, 
    Exp.LET(
      "y",
      Exp.BVAL(true), // y = Bool
      Exp.LET(
        "x",
        Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(4)), // x = Int (1)
        Exp.BINOP(Bop.SUM, Exp.ID("x"), Exp.ID("y")) // x + y = UNDEFINED
      )
    )
  );
  print("======== "); print(typeInfered); print(" == T.UNDEFINED ======== \n");

  print("===> LETREC SUCCESS\n"); // fat
  typeInfered := typeInfer.typeInfer(env, 
    Exp.LETREC(
      "fat",
      "x",
      Exp.IF(
        Exp.BINOP(Bop.EQ, Exp.ID("x"), Exp.NVAL(0)), 
        Exp.NVAL(1), 
        Exp.BINOP(Bop.MULT, 
          Exp.ID("x"), 
          Exp.APP(
            Exp.ID("fat"), 
            Exp.BINOP(Bop.MINUS, Exp.ID("x"), Exp.NVAL(1))
          )
        )
      ),
      Exp.APP(Exp.ID("fat"), Exp.NVAL(5))
    )
  );
  print("======== "); print(typeInfered); print(" == T.X (Int) ======== \n");

}