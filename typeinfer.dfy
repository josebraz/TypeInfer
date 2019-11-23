////////// LI Definitions //////////
type Ident = string
type Bool = bool
type Int = int
// Uncomment each command and add the TypeInfer implementation
datatype Bop = SUM | MINUS | MULT | DIV                // Algebric
             | EQ | DIF | LT | LE | GT | GE | AND | OR // Binary Logic
datatype Uop = NOT                                     // Unary Logic
datatype Exp    = NVAL(n: Int)
                | BVAL(b: Bool)
                | BINOP(bop: Bop, e1: Exp, e2: Exp) 
                | UNOP(uop: Uop, e: Exp)
                | PAIR(e1: Exp, e2: Exp) | FST(e: Exp) | SND(e: Exp)
                | IF(e1: Exp, e2: Exp, e3: Exp)
                | ID(x: Ident)
                // | APP(e1: Exp, e2: Exp)
                // | FN(x: Ident, e: Exp)
                // | LET(x: Ident, e1: Exp, e2: Exp)
                // | LETREC(f: Ident, y: Exp, e1: Exp, e2: Exp) // FIXME
                | NIL | CONS(e1: Exp, e2: Exp) | HD(e: Exp) | TL(e: Exp) | ISEMPTY(e: Exp)
                // | RAISE | TRY(e1: Exp, e2: Exp)

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
  {
    this.variables := 0;
    var t, c := collect(env, P);
    print("C: "); print(c); print("\n");
    var sigma, success := unify(c);
    if (success) {
      return t;
    } else {
      return T.UNDEFINED;
    } 
    // applysubs(σ, t);
  }

  method collect(env: Env, e: Exp) returns (t: T, eq: TypeEq)
    modifies this // to update the variables
  {
    match e {
      case NVAL(n) => t := T.Int; eq := {}; print("Collect NVAL\n");
      case BVAL(b) => t := T.Bool; eq := {}; print("Collect BVAL\n");
      case BINOP(bop: Bop, e1: Exp, e2: Exp) => {
        var t1, c1 := collect(env, e1);
        var t2, c2 := collect(env, e2); 
        var newTypeEq : TypeEq;
        match bop {
          case SUM   => newTypeEq := {typePair(t1, T.Int), typePair(t2, T.Int)};
          case MINUS => newTypeEq := {typePair(t1, T.Int), typePair(t2, T.Int)};
          case MULT  => newTypeEq := {typePair(t1, T.Int), typePair(t2, T.Int)};
          case DIV   => newTypeEq := {typePair(t1, T.Int), typePair(t2, T.Int)};
          case EQ    => newTypeEq := {typePair(t1, T.Bool), typePair(t2, T.Bool)};
          case DIF   => newTypeEq := {typePair(t1, T.Bool), typePair(t2, T.Bool)};
          case LT    => newTypeEq := {typePair(t1, T.Bool), typePair(t2, T.Bool)};
          case LE    => newTypeEq := {typePair(t1, T.Bool), typePair(t2, T.Bool)};
          case GT    => newTypeEq := {typePair(t1, T.Bool), typePair(t2, T.Bool)};
          case GE    => newTypeEq := {typePair(t1, T.Bool), typePair(t2, T.Bool)};
          case AND   => newTypeEq := {typePair(t1, T.Bool), typePair(t2, T.Bool)};
          case OR    => newTypeEq := {typePair(t1, T.Bool), typePair(t2, T.Bool)};
        }
        t := t2; eq := c1 + c2 + newTypeEq; print("Collect BINOP\n");
      }
      case UNOP(uop: Uop, e1: Exp) => {
        var t1, c1 := collect(env, e1);
        var newTypeEq := {typePair(t1, T.Bool)};
        t := t1; eq := c1 + newTypeEq; print("Collect UNOP\n");
      }
      case IF(e1: Exp, e2: Exp, e3: Exp) => {
        var t1, c1 := collect(env, e1);
        var t2, c2 := collect(env, e2); 
        var t3, c3 := collect(env, e3); 
        var newTypeEq := {typePair(t1, T.Bool), typePair(t2, t3)};
        t := t2; eq := c1 + c2 + c3 + newTypeEq;
      }
      case PAIR(e1: Exp, e2: Exp) => {
        var t1, c1 := collect(env, e1);
        var t2, c2 := collect(env, e2); 
        t := T.Pair(t1, t2); eq := c1 + c2;
      }
      case FST(e1: Exp) => {
        match e1 {
          case PAIR(first: Exp, second: Exp) => {
            t, eq := collect(env, first);
          }
          case NVAL(n) =>
          case BVAL(b) =>
          case BINOP(bop: Bop, e1: Exp, e2: Exp) =>
          case UNOP(uop: Uop, e1: Exp) =>
          case IF(e1: Exp, e2: Exp, e3: Exp) =>
          case FST(e1: Exp) =>
          case SND(e1: Exp) =>
          case ID(x: Ident) =>
          case NIL =>
          case CONS(e1: Exp, e2: Exp) => 
          case HD(e1: Exp) => 
          case TL(e1: Exp) =>
          case ISEMPTY(e1: Exp) =>
        }
      }
      case SND(e1: Exp) => {
        match e1 {
          case PAIR(first: Exp, second: Exp) => {
            t, eq := collect(env, second);
          }
          case NVAL(n) =>
          case BVAL(b) =>
          case BINOP(bop: Bop, e1: Exp, e2: Exp) =>
          case UNOP(uop: Uop, e1: Exp) =>
          case IF(e1: Exp, e2: Exp, e3: Exp) =>
          case FST(e1: Exp) =>
          case SND(e1: Exp) =>
          case ID(x: Ident) =>
          case NIL =>
          case CONS(e1: Exp, e2: Exp) =>
          case HD(e1: Exp) =>
          case TL(e1: Exp) =>
          case ISEMPTY(e1: Exp) =>
        }
      }
      case ID(x: Ident) => {
        if (x in env) {
          t := env[x]; eq := {};
        } else {
          print("ERRRRRR");
        }
      }
      case NIL => {
        // X new
        this.variables := this.variables + 1;
        t := T.List(T.X(this.variables)); eq := {};
      } 
      case CONS(e1: Exp, e2: Exp) => {
        var t1, c1 := collect(env, e1);
        var t2, c2 := collect(env, e2);
        var newTypeEq := {typePair(List(t1), t2)};
        t := t2; eq := c1 + c2 + newTypeEq;
      }
      case HD(e1: Exp) => {
        var t1, c1 := collect(env, e1);
        // X new
        this.variables := this.variables + 1;
        var newTypeEq := {typePair(t1, List(T.X(this.variables)))};
        t := T.X(this.variables); eq := c1 + newTypeEq;
      }
      case TL(e1: Exp) => {
        var t1, c1 := collect(env, e1);
        // X new
        this.variables := this.variables + 1;
        var newTypeEq := {typePair(t1, List(T.X(this.variables)))};
        t := T.X(this.variables); eq := c1 + newTypeEq;
      }
      case ISEMPTY(e1: Exp) => {
        var t1, c1 := collect(env, e1);
        // X new
        this.variables := this.variables + 1;
        var newTypeEq := {typePair(t1, List(T.X(this.variables)))};
        t := T.Bool; eq := c1 + newTypeEq;
      }
    }
  }

  method unify(eq: TypeEq) returns (eqReturns: TypeEq, success: bool)  
    modifies this
  {
    print("Received equation: "); print(eq); print("\n");
    // remove trivial equivalent types
    eqReturns := set pair:TypePair | pair in eq && pair.a != pair.b :: typePair(pair.a, pair.b);
    print("After unify equation: "); print(eqReturns); print("\n");
    success := eqReturns == {};
    
    // while (eqMutable != {})
    //   decreases eqMutable;
    // {
    //   var pairType :| pairType in eqMutable;
    //   if {
    //     case pairType.a == T.Int && pairType.b == T.Int   => eqMutable := eqMutable - {pairType}; print("Unify Int\n");
    //     case pairType.a == T.Bool && pairType.b == T.Bool => eqMutable := eqMutable - {pairType}; print("Unify Bool\n");
    //     case pairType.a == T.List(T.Int) && pairType.b == T.List(T.Int)   => eqMutable := eqMutable - {pairType}; print("Unify Int List"); // optimization by the case 1
    //     case pairType.a == T.List(T.Bool) && pairType.b == T.List(T.Bool) => eqMutable := eqMutable - {pairType}; print("Unify Bool List"); // optimization by the case 1
        
        
        
    //     // case pairType.a == T.Fun(T.Int, T.Int) && pairType.b == T.Int   => eqMutable := eqMutable - {pairType}; print("Unify Int\n");
    //     case true => success := false; print("Unify fails\n"); return; 
    //   }
    // }
  }
}

method Main() {
  var typeInfer := new TypeInfer;
  var env := map[];
  var typeInfered: T;

  ///////////// Tests /////////////
  typeInfered := typeInfer.typeInfer(env, Exp.BINOP(Bop.SUM, Exp.NVAL(5), Exp.NVAL(8)));
  print(typeInfered);
  print(" == T.Int\n");

  typeInfered := typeInfer.typeInfer(env, Exp.BINOP(Bop.SUM, Exp.NVAL(5), Exp.BVAL(true)));
  print(typeInfered);
  print(" == T.UNDEFINED\n");

  typeInfered := typeInfer.typeInfer(env, 
    Exp.BINOP(
      Bop.MULT,
      Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)), 
      Exp.BINOP(Bop.SUM, Exp.NVAL(5), Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)))
    )
  );
  print(typeInfered);
  print(" == T.Int\n");

  typeInfered := typeInfer.typeInfer(env, 
    Exp.FST(
      Exp.PAIR(
        Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)), 
        Exp.BINOP(Bop.LT, Exp.BVAL(true), Exp.BVAL(false))
      )
    )
  );
  print(typeInfered);
  print(" == T.Int\n");

  typeInfered := typeInfer.typeInfer(env, 
    Exp.SND(
      Exp.PAIR(
        Exp.BINOP(Bop.MINUS, Exp.BINOP(Bop.MINUS, Exp.NVAL(5), Exp.NVAL(8)), Exp.NVAL(8)), 
        Exp.BINOP(Bop.LT, Exp.BVAL(true), Exp.BVAL(false))
      )
    )
  );
  print(typeInfered);
  print(" == T.Bool\n");
}