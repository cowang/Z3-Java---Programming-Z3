package cowan.george;


import org.junit.*;
import org.eclipse.jdt.annotation.Nullable;
import org.hamcrest.MatcherAssert;
import org.hamcrest.core.CombinableMatcher;

import static org.hamcrest.CoreMatchers.*;
import static org.junit.Assert.*;
import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import com.microsoft.z3.*;



/**
 * Working through the example code in Chapter 2 of the
 * <a href="http://theory.stanford.edu/~nikolaj/programmingz3.html">Programming Z3</a> tutorial.
 *
 * <p>Note that the goal is to locate the corresponding Java methods to accomplish what the Python
 * code in the tutorial accomplishes. Therefore, we do not attempt to make the Java as readable as
 * the Python in the tutorial, using the corresponding Java calls without much wrapping. There is a
 * "Utility Methods" section at the end of this compile unit that contains some helper methods to
 * simplify coding.
 */
@SuppressWarnings({"null", "static-method", "unused", "unchecked"})
public class ProgrammingZ3Chapter02_00 {

// We make the context available to all methods
static HashMap<String, String> cfg;
static Context ctx;

/**
 * Make a context ctx available to all methods. The context is based on the configuration
 *
 * <code><pre>
 * model=true
 * </pre></code>
 *
 * which has a solver always create a model when it finds a solution or a counter-example when a
 * theorem is disproven.
 */
@BeforeClass
public static void setUpBeforeClass() throws Exception {
  cfg = new HashMap<>();
  cfg.put("model", "true"); // set model=true in the configuration

  ctx = new Context(cfg);
}

@AfterClass
public static void tearDownAfterClass() throws Exception {
  ctx.close();
}

//////////////////////////////////////////
// Chapter 2 - Logical Interfaces to Z3 //
//////////////////////////////////////////

/**
 * The Python code corresponding to this test is
 * <pre><code>
    from z3 import *
    Tie, Shirt = Bools('Tie Shirt')
    s = Solver()
    s.add(Or(Tie, Shirt),
          Or(Not(Tie), Shirt),
          Or(Not(Tie), Not(Shirt)))
    print(s.check())
    print(s.model())
 * </code></pre>
 */
@Test
public void tieShirt_testCh02_00() throws Exception {

  try(Context ctx = new Context(cfg)) {
    // Tie, Shirt = Bools('Tie Shirt')
    BoolExpr tie = ctx.mkBoolConst("Tie");
    BoolExpr shirt = ctx.mkBoolConst("Shirt");

    // s = Solver()
    Solver s = ctx.mkSolver();

    // s.add(Or(Tie, Shirt),
    //       Or(Not(Tie), Shirt),
    //       Or(Not(Tie), Not(Shirt)))
    s.add( ctx.mkOr(tie, shirt)
         , ctx.mkOr(ctx.mkNot(tie), shirt)
         , ctx.mkOr(ctx.mkNot(tie), ctx.mkNot(shirt))
         );

    // print(s.check())
    Status actualStatus = s.check();
    Status expectStatus = Status.SATISFIABLE;
    assertEquals(expectStatus, actualStatus);

    // print(s.model())
    Model sModel = s.getModel();


    // Here are three different approaches to getting the assignments

    // As a List of Strings
    String actual = assignments(sModel).toString();
    String expect = "[Tie=false, Shirt=true]";
    assertEquals(expect, actual);

    // As a map from symbols to expressions
    actual = assignmentMap(sModel).toString();
    expect = "{Tie=false, Shirt=true}";
    assertEquals(expect, actual);

    // As an SMT-LIB expression
    actual = sModel.toString();
    expect =  """
        (define-fun Tie () Bool
          false)
        (define-fun Shirt () Bool
          true)""";
    assertEquals(expect, actual);
  }
}

/**
 * We do the same thing as before but using the solve() method instead. The solve method is defined
 * in the utility functions section below. Here is the equivalent Python code from the tutorial:
 * <pre><code>
    Tie, Shirt = Bools('Tie Shirt')
    solve(Or(Tie, Shirt),
          Or(Not(Tie), Shirt),
          Or(Not(Tie), Not(Shirt)))
 * </code></pre>
 */
@Test
public void tieShirt_testCh02_00a() throws Exception {

  // Tie, Shirt = Bools('Tie Shirt')
  BoolExpr tie   = ctx.mkBoolConst("Tie");
  BoolExpr shirt = ctx.mkBoolConst("Shirt");

  // solve(Or(Tie, Shirt),
  //     Or(Not(Tie), Shirt),
  //     Or(Not(Tie), Not(Shirt)))
  String actual = solve( ctx.mkOr(tie, shirt)
                       , ctx.mkOr(ctx.mkNot(tie), shirt)
                       , ctx.mkOr(ctx.mkNot(tie), ctx.mkNot(shirt))
                       );
  String expect = "[Tie=false, Shirt=true]";
  assertEquals(expect, actual);
}

/**
 * The following example uses the theory of arrays and of functions, but checking the logic just
 * requires propositional logic.
 *
 * <pre>
 * <code>
    Z = IntSort()
    f = Function('f', Z, Z)
    x, y, z = Ints('x y z')
    A = Array('A', Z, Z)
    fml = Implies(x + 2 == y, f(Store(A, x, 3)[y - 2]) == f(y - x + 1))
    solve(Not(fml))
   </code>
 * </pre>
 *
 * Below we see that coding the implication in Java with all its operations translated to method
 * calls is not pretty, making us itch to write a language that is translated using something like
 * Antlr.
 */
@Test
public void propositionalLogic_testNoSolution() throws Exception {

  //  Z = IntSort()
  IntSort zSort = ctx.getIntSort();

  //  f = Function('f', Z, Z)
  FuncDecl<IntSort> f = ctx.mkFuncDecl("f", zSort, zSort);

  //  x, y, z = Ints('x y z')
  IntExpr x = ctx.mkIntConst("x");
  IntExpr y = ctx.mkIntConst("y");
  IntExpr z = ctx.mkIntConst("z");

  //  A = Array('A', Z, Z)
  ArrayExpr<IntSort, IntSort> arrayA = ctx.mkArrayConst("A", zSort, zSort);

  IntNum i1 = ctx.mkInt(1);
  IntNum i2 = ctx.mkInt(2);
  IntNum i3 = ctx.mkInt(3);
  //  fml = Implies(x + 2 == y, f(Store(A, x, 3)[y - 2]) == f(y - x + 1))
  var fml = ctx.mkImplies(ctx.mkEq(ctx.mkAdd(x,i2),
                                   y),
                          ctx.mkEq(ctx.mkApp(f, ctx.mkSelect(ctx.mkStore(arrayA, x, i3),
                                                             ctx.mkSub(y, i2) )),
                                   ctx.mkApp(f, ctx.mkAdd(ctx.mkSub(y, x), i1)) ));
  //  fml happens to be a tautology, so Not(fml) is not satisfied by any assignment of values
  //  solve(Not(fml))
  String actual = solve(ctx.mkNot(fml));
  String expected = Status.UNSATISFIABLE.toString();
  assertEquals(expected, actual);
}

/**
 * We don't have a simple language for formulas, but at least we can enter formulas in the SMT-LIB2
 * language. Here is a test for entering the formula
 * <code><pre>
 * (x % 4) + 3 * (y / 2) > x - y
 * </pre></code>
 *
 * which in SMT-LIB2, uses prefix notation.
 */
@Test
public void testName_enterSMT_LIB2() throws Exception {
  var smt =
    """
    (declare-const x Int)
    (declare-const y Int)
    (assert (> (+ (mod x 4) (* 3 (div y 2))) (- x y)))
    """;
  Solver s = solverForSMTString(smt);
  assertEquals(Status.SATISFIABLE, s.check());

  Model sModel = s.getModel();
  String actual = assignments(sModel).toString();

  // Unfortunately, Z3 does not give solutions deterministically.
  // If the following assert fails, you will have to add the additional possibility to the list.
  assertTrue(List.of("[x=0, y=1]", "[x=-4, y=0]").contains(actual));

  String actualModel  = sModel.toString();
  String actualSolver = s.toString();

  String expect;

  expect = "[x=-4, y=0]";
  if (actual == expect) {
    String expectModel1 =  """
                            (define-fun x () Int
                              (- 4))
                            (define-fun y () Int
                              0)""";
    assertEquals(expectModel1, actualModel);

    String expectSolver1 = """
                            (declare-fun y () Int)
                            (declare-fun x () Int)
                            (assert (> (+ (mod x 4) (* 3 (div y 2))) (- x y)))
                            (rmodel->model-converter-wrapper
                            x -> (- 4)
                            y -> 0
                            )
                            """;
    assertEquals(expectSolver1, actualSolver);
  }

}


                 ////////////////
                 // 2.1. Sorts //
                 ////////////////







/////////////////////////// Utility Methods /////////////////////////////

/**
 * Returns a string containing the variable assignments for the solution. If the solver is able to
 * determine that the conjuncts have no solution, it returns "UNSATISFIABLE". "UNKNOWN" indicates
 * that the solver was not able to determine whether the constraints were {@code SATISFIABLE} or
 * <code>UNSATISFIABLE</code>.
 */
private String solve(Expr<BoolSort>... conjuncts) {
  Solver s = solverFor(conjuncts);
  return solution(s);
}

private Solver solverFor(Expr<BoolSort>... conjuncts) {
  Solver s = ctx.mkSolver();
  s.add(conjuncts);
  return s;
}

/**
 * The solution for the solvers current set of constraints, or a status string if it was unable to
 * find a solution.
 */
private String solution(Solver solver) {
  Status status = solver.check();
  if (status == Status.SATISFIABLE)
    return assignments(solver.getModel()).toString();
  else
    return status.toString();
}

private void solutionFor(Expr<BoolSort>... conjuncts) {
  System.out.println(assignments(solverFor(conjuncts).getModel()));
}

private Solver solverForSMTString(String smt) {
  Solver s = ctx.mkSolver();
  s.add(ctx.parseSMTLIB2String(smt, null, null, null, null));
  return s;
}



/**
 * The map from the names of the solution variables to their values, or {@code null} if no solution
 * was found. For instance, the string representation of the map might be
 *
 * <code><pre>
 * {a = 2, next = true}
 * </pre></code>
 */
private static @Nullable Map<Symbol, Expr<?>> assignmentMap(Solver solver) {
  Model m = solver.getModel();
  return (m == null) ? null
                     : assignmentMap(m);
}

/**
 * A List containing the solution as a string for each variable/constant and its value. For
 * instance,
 *
 * <code><pre>
 * a=2
 * next=true
 * </pre></code>
 */
private static List<String> assignments(Model model) {
  FuncDecl<?>[] variables = model.getConstDecls();
  List<String> list = new ArrayList<>(variables.length);
  for (var v : variables) {
    list.add(v.getName().toString() +"="+ model.getConstInterp(v).toString());
  }
  return list;
}

/**
 * A map from the names of the solution variables to their values. For instance, the string
 * representation of the map might be
 * <pre>
 * {a=2, next=true}
 * </pre>
 */
private static Map<Symbol, Expr<?>> assignmentMap(Model model) {
  FuncDecl<?>[] variables = model.getConstDecls();
  Map<Symbol, Expr<?>> map = new LinkedHashMap<>();
  if (map != null)
    for (var v : variables) {
      map.put(v.getName(), model.getConstInterp(v));
    }
  return map;
}

}
