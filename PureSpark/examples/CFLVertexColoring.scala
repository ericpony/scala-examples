package purespark.examples

import purespark.GraphX._
import purespark.Prelude._

import scala.util.Random

object Types {
  type Color = Int
  type Palette = (Color, List[Double], Boolean, Random)
}

/**
 * A pregel implemention of the Communication-Free Learning algorithm for graph coloring.
 *
 * See D. J. Leith and P. Clifford. Convergence of distributed learning algorithms for
 * optimal wireless channel allocation. In IEEE CDC, pages 2980–2985, 2006.
 */
object RandomizedGraphColoring {

  import Types._

  private def sampleColor (dist: List[Double], rnd: Double): Int = {
    foldl(dist)((1, 0.0)) {
      case ((color, mass), weight) => {
        val m = mass + weight
        (if (m < rnd) color + 1 else color, m)
      }
    }._1
  }

  def run (graph: GraphRDD[Color, _], beta: Double, maxNumColors: Int): GraphRDD[Color, _] = {

    val initColorDist = map((1 to maxNumColors).toList)(_ => 1.0 / maxNumColors)
    val distGraph = GraphRDD(mapVertices(graph.vertexRDD) {
      v => (v.attr, initColorDist, true, new Random(Random.nextLong))
    }, graph.edgeRDD)

    def sendMessage (edge: EdgeTriplet[Palette, _]): List[Vertex[Boolean]] = {
      if (edge.srcAttr._1 == edge.dstAttr._1)
        return List(Vertex(edge.srcId, true))
      if (edge.srcAttr._3)
        return List(Vertex(edge.srcId, false))
      List.empty
    }
    def vprog (v: Vertex[Palette], active: Boolean): Palette = {
      val color = v.attr._1
      val dist = v.attr._2
      val rng = v.attr._4
      val new_dist = foldl(dist)((1, List[Double]())) {
        case ((i, list), weight) => (i + 1,
          if (active)
            list :+ (weight * (1 - beta) + (if (color == i) 0.0 else beta / (maxNumColors - 1)))
          else
            list :+ (if (color == i) 1.0 else 0.0))
      }._2
      val new_color = if (active) sampleColor(new_dist, rng.nextDouble) else color

      (new_color, new_dist, active, rng)
    }
    val resGraph = Pregel(distGraph)(true)(vprog)(sendMessage)(_ || _)

    GraphRDD(mapVertices(resGraph.vertexRDD)(v => v.attr._1), resGraph.edgeRDD)
  }
}

object GraphColoringExample extends App {

  // convert an RDD of tuples to an EdgeRDD
  private def fromTuplesToEdges (edges: RDD[(VertexId, VertexId)]): EdgeRDD[Null] =
    map(edges)(map(_) { case (s, t) => Edge(s, t, null)})

  // convert directed edges to undirected edges
  private def fromDGToUG (edges: RDD[(VertexId, VertexId)]): EdgeRDD[Null] =
    map(edges)(concatMap(_) {
      case (s, t) => List(Edge(s, t, null), Edge(t, s, null))
    })

  // compute the maximum degree of an undirected graph
  private def maxDegreeOf[A, B] (graph: GraphRDD[A, B]): Int =
    foldl(concat(aggregateMessages(graph)(e => List(Vertex(e.dstId, 1)))(_ + _)))(0)({
      case (d, v) => scala.math.max(d, v.attr)
    })

  def run = {
    // arbitraty chosen
    val beta = 0.5
    /*
    val edges = fromDGToUG(List(
      // an edge RDD with three partitions
      List((2, 1), (2, 3), (3, 1), (6, 7)),
      List((5, 7), (4, 2), (4, 7), (5, 1)),
      List((5, 6), (3, 6))
    ))
    */

    // generate a complete graph
    val numVertices = 9
    val vids: List[VertexId] = (1 to numVertices).toList
    val edges = fromTuplesToEdges(map(vids) {
      i => foldl(vids)(List[(VertexId, VertexId)]()) {
        (list, j) => if (j != i) list :+(i, j) else list
      }
    })

    // all vertices have the same color at the beginning
    val vertices = List((1 to numVertices).toList.map(Vertex(_, 1)))

    // an example undirected graph
    val graph = GraphRDD(vertices, edges)

    val maxNumColors = maxDegreeOf(graph) + 1
    val result = RandomizedGraphColoring.run(graph, beta, maxNumColors)

    println("Number of available colors: " + maxNumColors)
    println("A proper coloring of the provided graph:")

    concat(result.vertexRDD).foreach(println)
  }

  GraphColoringExample.run
}

