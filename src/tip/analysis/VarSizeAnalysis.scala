package tip.analysis

import tip.ast.{AExpr, AInput}
import tip.ast.AstNodeData.DeclarationData
import tip.cfg._
import tip.lattices.IntervalLattice.{IntNum, MInf, Num, PInf}
import tip.lattices.VarSizeLattice.{TNothing, resolveType}
import tip.lattices.{LiftLattice, VarSizeLattice}
import tip.solvers.{WorklistFixpointSolverWithReachabilityAndWidening, WorklistFixpointSolverWithReachabilityAndWideningAndNarrowing}

trait VarSizeIntervalAnalysisWidening extends ValueAnalysisMisc with Dependencies[CfgNode] {

  import tip.cfg.CfgOps._

  val cfg: ProgramCfg

  val valuelattice: VarSizeLattice.type

  val liftedstatelattice: LiftLattice[statelattice.type]

  private val B = cfg.nodes.flatMap { n =>
    n.appearingConstants.map { x =>
      IntNum(x.value): Num
    } + MInf + PInf
  }

  private def minB(b: Num) = B.filter(b <= _).min

  private def maxB(a: Num) = B.filter(_ <= a).max

  override def eval(exp: AExpr, env: statelattice.Element)(implicit declData: DeclarationData): valuelattice.Element = {
    import valuelattice._
    exp match {
      case _: AInput => (MInf, PInf, TBigInt)
      case _ => super.eval(exp, env)
    }
  }

  def loophead(n: CfgNode): Boolean = indep(n).exists(cfg.rank(_) > cfg.rank(n))

  def widenInterval(x: valuelattice.Element, y: valuelattice.Element): valuelattice.Element =
    (x, y) match {
      case ((_, _, TNothing), _) => y
      case (_, (_, _, TNothing)) => x
      case ((l1, h1, _), (l2, h2, _)) =>
        val min = if (l1 <= l2) l1 else maxB(l2)
        val max = if (h2 <= h1) h1 else minB(h2)
        (min, max, resolveType(min, max))
    }

  def widen(x: liftedstatelattice.Element, y: liftedstatelattice.Element): liftedstatelattice.Element =
    (x, y) match {
      case (liftedstatelattice.Bottom, _) => y
      case (_, liftedstatelattice.Bottom) => x
      case (liftedstatelattice.Lift(xm), liftedstatelattice.Lift(ym)) =>
        liftedstatelattice.Lift(declaredVars.map { v =>
          v -> widenInterval(xm(v), ym(v))
        }.toMap)
    }
}

object VarSizeAnalysis{
  object Intraprocedural {

    class WorklistSolverWithWidening(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
      extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, VarSizeLattice)
        with WorklistFixpointSolverWithReachabilityAndWidening[CfgNode]
        with VarSizeIntervalAnalysisWidening

    class WorklistSolverWithWideningAndNarrowing(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
      extends IntraprocValueAnalysisWorklistSolverWithReachability(cfg, VarSizeLattice)
        with WorklistFixpointSolverWithReachabilityAndWideningAndNarrowing[CfgNode]
        with VarSizeIntervalAnalysisWidening {

      val narrowingSteps = 5
    }
  }
}


