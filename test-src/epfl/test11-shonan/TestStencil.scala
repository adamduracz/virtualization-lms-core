package scala.virtualization.lms
package epfl
package test11

import common._
import test1._
import test7._
import test8.{ArrayMutation,ArrayMutationExp,ScalaGenArrayMutation,OrderingOpsExpOpt}

import util.OverloadHack
import scala.reflect.SourceContext

import java.io.{PrintWriter,StringWriter,FileOutputStream}
import scala.reflect.SourceContext


class TestStencil extends FileDiffSuite {
  
  trait DSL extends LiftNumeric with NumericOps with ArrayOps with RangeOps with BooleanOps 
    with LiftVariables with IfThenElse with Print {
    def staticData[T:Manifest](x: T): Rep[T]
    def test(x: Rep[Array[Int]]): Rep[Array[Int]]
  }
  trait Impl extends DSL with Runner with ArrayOpsExpOpt with NumericOpsExpOpt 
      with OrderingOpsExpOpt with BooleanOpsExp 
      with EqualExpOpt with VariablesExpOpt with RangeOpsExp with StaticDataExp
      with IfThenElseExpOpt with PrintExp 
      with CompileScala { self => 
    //override val verbosity = 1
    val codegen = new ScalaGenNumericOps with ScalaGenStaticData with ScalaGenOrderingOps with ScalaGenArrayOps with ScalaGenRangeOps
      with ScalaGenVariables with ScalaGenIfThenElse
      with ScalaGenPrint /*with LivenessOpt*/ { val IR: self.type = self }
    codegen.emitSource(test, "Test", new PrintWriter(System.out))
    run()
  }
  trait Runner extends Compile {
    def test(x: Rep[Array[Int]]): Rep[Array[Int]]
    def run() {
      val f = compile(test)
      val v0 = Array(3, 1, 5, -2, 4)
      val v1 = f(v0)
      v1 foreach println
    }
  }


  trait Sliding extends DSL {
    
    def infix_sliding[T:Manifest](n: Rep[Int], f: Rep[Int] => Rep[T]): Rep[Array[T]]
    
  }
  
  trait SlidingExp extends ArrayOpsExpOpt with NumericOpsExpOpt 
      with OrderingOpsExpOpt with BooleanOpsExp 
      with EqualExpOpt with VariablesExpOpt with RangeOpsExp
      with IfThenElseExpOpt {
    
    /*
    idea:
      
      loop(n) { i => f(i) }
      
      evaluate f(i), stms0 be all statements computed
      treat all defined syms as outputs: (s1,s2,s3,r)
      
      loop(n) { i => (s1,s2,s3,r) }
      
      

      
      
    */
    
    
    
    
    def infix_sliding[T:Manifest](n: Rep[Int], f: Rep[Int] => Rep[T]): Rep[Array[T]] = {
      val a = NewArray[T](n)
      (unit(0) until (n-unit(1))) foreach { i =>
        
        // evaluate loop contents f(i)
        val (r0,stms0) = reifySubGraph(f(i))
        reflectSubGraph(stms0)
        stms0.foreach(println)
        
        val defs = stms0.flatMap(_.lhs)
        
        a(i) = r0
        
        // evaluate loop contents f(i+1)
        val (r1,stms1) = reifySubGraph(f(i+1))
        reflectSubGraph(stms1)
        
        println("r1:")
        stms1.foreach(println)

        // see what f(i+1) can reuse from f(i)
        val overlap = stms1.flatMap { case TP(s,d) => syms(d) filter (defs contains _) }

        println("overlap:")
        overlap.foreach(println)
        
        // build a variable for each overlap sym.
        // init variables by peeling first loop iteration.
        // replace overlap
        
        // need to figure out new values to assign to vars ...
        
        a(i+1) = r1
      }
      a
    }
    
    
  }


  val prefix = "test-out/epfl/test11-"
  

  def testStencil1 = {
    withOutFileChecked(prefix+"stencil1") {
      trait Prog extends DSL with Sliding {
        def test(v: Rep[Array[Int]]) = {

          val n = 20
          
          def compute(i: Rep[Int]) = 2 * i + 3
          
          val res = n sliding { i =>
            compute(i) + compute(i+1)
          }
          
          res
        }
      }
      new Prog with Impl with SlidingExp
    }
  }




  def testStencil2 = {
    withOutFileChecked(prefix+"stencil2") {
      trait Prog extends DSL {
        def test(v: Rep[Array[Int]]) = {

          /*
          const int N = 20;
          void program0(vector<double> input, vector<double>& output) {
            vector<double> input2(N);
            vector<double> wind(N);
            for (int i = 0; i < N; ++i) {
              input2[i]=input[i];
            }
            for (int i = 0; i < N-1; ++i) {
              wind[i] = input2[i] * input2[i+1];
            }
            for (int i = 1; i < N+1; ++i) {
              output[i] = input2[i] - wind[i] + wind[i-1];
            }
          }
          */
          
          
          /*
          .~(loop0 2 0 n .<a>. .<b>. (fun a ->
          let w1 j = a j *@ a (j+1) in 
          let wm j = a j -@ w1 j +@ w1 (j-1) in 
          let w2 j = wm j *@ wm (j+1) in 
          wm 0 -@ w2 0 +@ w2 (-1)))
          */
          
          /*
          
          def compute(b: Rep[Array[Int]], a: Rep[Array[Int]], n: Rep[Int]) = {
            def w(j: Rep[Int]) = a(j) * a(j+1)
            for (i <- 0 until n: Rep[Range]) {
              b(i) = a(i) - w(i) + w(i-1)
            }
          }
          */


          val A = scala.Array
          
          val a = A(A(1,0,0,1,0),
                    A(0,0,1,0,0),
                    A(0,1,0,0,0),
                    A(0,0,1,1,1),
                    A(0,0,1,0,1))

          val n = 5

          val v1 = NewArray[Int](n)
          v1
        }
      }
      new Prog with Impl
    }
  }


 
}