package sigmastate.eval

import scalan.Lazy
import sigmastate.helpers.SigmaTestingCommons

/** This test cases specify evaluation semantics of OpCost operation. */
class CostAccumulatorTest extends SigmaTestingCommons { suite =>

  lazy val IR = new TestingIRContext()
  import IR._
  import Liftables._

  /** Take graph building lambda, compile it and apply to the given arg */
  def run[ST, T](name: String, fLam: Rep[T] => Rep[Int], x: ST, expectedRes: Int)(implicit lT: Liftable[ST,T]): Unit = {
    val fSym = fun(fLam)(Lazy(lT.eW))
    emit(name, fSym) // save graph to file
    val f = IR.compile(getDataEnv, fSym, None)
    val (y, _) = f(x)
    y shouldBe expectedRes
  }

  def run2[ST, T, SU, U](name: String,
                         fLam: (Rep[T], Rep[U]) => Rep[Int], x: (ST, SU), expectedRes: Int)
                        (implicit lT: Liftable[ST, T], lU: Liftable[SU, U]): Unit = {
    implicit val eT = lT.eW
    implicit val eU = lU.eW
    val fSym = fun((p: Rep[(T,U)]) => fLam(p._1, p._2))
    emit(name, fSym) // save graph to file
    val f = IR.compile(getDataEnv, fSym, None)
    val (y, _) = f(x)
    y shouldBe expectedRes
  }

  lazy val v1 = variable[Int]
  lazy val v2 = variable[Int]
  lazy val v3 = variable[Int]

  /** How to read test cases:
    * In the tests  `cost` refers to CostAccumulator.currentScope.currentCost
    * cost = 0  at the beginning of all lambdas
    * + - means the value is added to the current cost
    * M - the node is marked as visited, and repeated additions are avoided.
    * S - the value is skipped and not added to the current cost
    */
  property("CostAccumulator single OpCode") {
    run("opCost_const", { _: Rep[Int] =>
      opCost(v1, Nil, 5/*+,M*/)
      }, 0/*not used*/, 5)    // cost = 5

    run("opCost_arg_const", { _: Rep[Int] =>
      opCost(v1, Seq(5/*+,M*/), 5/*S*/) // cost = 5
      }, 0/*not used*/, 5)

    run("opCost_arg_and_const", { _: Rep[Int] =>
      opCost(v1, Seq(5/*+,M*/), 10/*+*/)  // cost = 15
      }, 0/*not used*/, 15)

    run("opCost_id", { x: Rep[Int] => opCost(v1, Nil, x/*+*/) }, 10, 10)
    run("opCost_const_id", { x: Rep[Int] => opCost(v1, Seq(5/*+,M*/), x/*+*/) }, 10, 15)
    run2("opCost_const_id2", { (x: Rep[Int], y: Rep[Int]) => opCost(v1, Seq(y), x) }, (10, 5), 15)

    run("opCost_id_const", { x: Rep[Int] => opCost(v1, Seq(x), 6) }, 10, 16)
    run2("opCost_const_id2", { (x: Rep[Int], y: Rep[Int]) => opCost(v1, Seq(x), y) }, (10, 6), 16)

    run("opCost_arg_id", { x: Rep[Int] => opCost(v1, Seq(x), x) }, 10, 10)

    run("opCost_two_args", { x: Rep[Int] => opCost(v1, Seq(x, x), 5) }, 10, 15)
    run2("opCost_two_args_2", { (x: Rep[Int], y: Rep[Int]) => opCost(v1, Seq(x, x), y) }, (10, 5), 15)
    run2("opCost_two_args_3", { (x: Rep[Int], y: Rep[Int]) => opCost(v1, Seq(x, y), y) }, (10, 5), 15)
    run2("opCost_two_args_4", { (x: Rep[Int], y: Rep[Int]) => opCost(v1, Seq(x, y), x + y) }, (10, 5), 30)
  }

  property("CostAccumulator two OpCode") {
    run("2xOpCost_1", { _: Rep[Int] =>
      val c0: Rep[Int] = 5   // const node
      val c1 = opCost(v1, Nil, c0/*+*/) // cost = 5
      val c2 = opCost(v2, Nil, c0/*+*/) // cost = 10
      c1 + c2
      }, 10, 15)
    run("2xOpCost_2", { x: Rep[Int] =>
      val c1 = opCost(v1, Nil, x/*+*/) // cost = 10
      val c2 = opCost(v2, Nil, x/*+*/) // cost = 20
      c1 + c2
      }, 10, 30)
    run("2xOpCost_3", { x: Rep[Int] =>
      val c1 = opCost(v1, Nil, x/*+*/) // cost = 10, c1 marked
      opCost(v2, Seq(c1), x/*+*/)      // cost = 20
      }, 10, 20)
    run("2xOpCost_4", { x: Rep[Int] =>
      val c1 = opCost(v1, Nil, x/*+*/) // cost = 10, c1 marked
      opCost(v2, Nil, c1)              // cost = 10 because c1 is marked
      }, 10, 10)
    run("2xOpCost_5", { x: Rep[Int] =>
      val c0: Rep[Int] = 5   // const node
      val c1 = opCost(v1, Seq(c0/*+,M*/), x/*+*/) // cost = 15
      opCost(v2, Nil, c1)                           // cost = 15 because c1 is marked
      }, 10, 15)
    run2("2xOpCost_6", { (x: Rep[Int], y: Rep[Int]) =>
      val c1 = opCost(v1, Seq(y/*+,M*/), x/*+*/)  // cost = 15
      opCost(v2, Nil, c1)                           // cost = 15 because c1 is marked
      }, (10, 5), 15)

    run2("2xOpCost_7", { (x: Rep[Int], y: Rep[Int]) =>
      val c1 = opCost(v1, Seq(y/*+,M*/), x/*+*/)  // cost = 15
      opCost(v2, Seq(x/*+,M*/), c1/*S*/)          // cost = 25 because x is not marked
      }, (10, 5), 25)
  }

  property("CostAccumulator three OpCode") {
    run2("3xOpCost_1", { (x: Rep[Int], y: Rep[Int]) =>
      val c0: Rep[Int] = 5   // const node
      val o1 = opCost(v1, Seq(x/*+10,M*/), c0/*+5*/)         // cost = 15
      val o2 = opCost(v2, Seq(c0/*+5,M*/, x/*S*/, o1/*S*/), y/*+5*/)  // cost = 25
      opCost(v3, Seq(y/*+5,M*/, o2/*S*/), c0/*S*/)          // cost = 30
      }, (10, 5), 30)

    // o1 is used in OpCost.args
    run2("3xOpCost_2", { (x: Rep[Int], _: Rep[Int]) =>
      val c0: Rep[Int] = 5   // const node
      val o1 = opCost(v1, Nil, c0/*+5*/)            // cost = 5
      val o2 = opCost(v2, Seq(o1/*S*/), x/*+10*/)  // cost = 15
      val o3 = opCost(v3, Seq(o1/*S*/, o2/*S*/), c0/*+5*/) // cost = 20
      o3 * 3
      }, (10, 5), 60)

    // same as above but using y
    run2("3xOpCost_3", { (x: Rep[Int], y: Rep[Int]) =>
      val c0: Rep[Int] = 5   // const node
      val o1 = opCost(v1, Nil, c0/*+5*/)           // cost = 5
      val o2 = opCost(v2, Seq(o1/*S*/), x/*+10*/)  // cost = 15
      val o3 = opCost(v3, Seq(o1/*S*/, o2/*S*/), y/*+5*/) // cost = 20
      o3 * 3
      }, (10, 5), 60)

    // o1 is used in outside OpCost
    run2("3xOpCost_4", { (x: Rep[Int], y: Rep[Int]) =>
      val c0: Rep[Int] = 5   // const node
      val o1 = opCost(v1, Nil, c0/*+5*/) // cost = 5, value = 5
      val o2 = opCost(v2, Seq(o1/*S*/), x/*+10*/)  // cost = 15
      val o3 = opCost(v3, Seq(o1/*S*/, o2/*S*/), y/*+5*/) // cost = 20
      o3 * o1  // == 20 * 5
      }, (10, 5), 100)

    // same as above but o1 is used in OpCost.opCost
    run2("3xOpCost_5", { (x: Rep[Int], y: Rep[Int]) =>
      val c0: Rep[Int] = 5   // const node
      val o1 = opCost(v1, Nil, c0/*+5*/) // cost = 5, value = 5
      val o2 = opCost(v2, Seq(o1/*S*/), x/*+10*/)  // cost = 15
      val o3 = opCost(v3, Seq(o1/*S*/, o2/*S*/), y + o1/*+10*/) // cost = 25
      o3 * o1  // == 25 * 5
      }, (10, 5), 125)

  }
}
