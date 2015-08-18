package purespark.examples

import purespark.GraphX._
import purespark.Prelude._

/**
 * Computes shortest paths to the given set of landmark vertices, returning a graph where each
 * vertex attribute is a map containing the shortest-path distance to each reachable landmark.
 */
object ShortestPaths {

  /** Stores a map from the vertex id of a landmark to the distance to that landmark. */
  type SPMap = Map[VertexId, Int]

  private def makeMap (x: (VertexId, Int)*) = Map(x: _*)

  private def incrementMap (spmap: SPMap): SPMap = spmap.map { case (v, d) => v -> (d + 1)}

  private def addMaps (spmap1: SPMap, spmap2: SPMap): SPMap =
    (spmap1.keySet ++ spmap2.keySet).map {
      k => k -> scala.math.min(spmap1.getOrElse(k, Int.MaxValue), spmap2.getOrElse(k, Int.MaxValue))
    }.toMap

  /**
   * Computes shortest paths to the given set of landmark vertices.
   *
   * @tparam E the edge attribute type (not used in the computation)
   *
   * @param graph the graph for which to compute the shortest paths
   * @param landmarks the list of landmark vertex ids. Shortest paths will be computed to each
   *                  landmark.
   *
   * @return a graph where each vertex attribute is a map containing the shortest-path distance to
   *         each reachable landmark vertex.
   */
  def run[V, E] (graph: GraphRDD[V, E], landmarks: Seq[VertexId]): GraphRDD[SPMap, E] = {
    val spGraph = GraphRDD(
      mapVertices(graph.vertexRDD) { v =>
        if (landmarks.contains(v.id)) makeMap(v.id -> 0) else makeMap()
      },
      graph.edgeRDD)
    val initialMessage = makeMap()

    def sendMessage (edge: EdgeTriplet[SPMap, _]): List[Vertex[SPMap]] = {
      val newAttr = incrementMap(edge.dstAttr)
      if (edge.srcAttr != addMaps(newAttr, edge.srcAttr))
        List(Vertex(edge.srcId, newAttr))
      else
        List.empty
    }
    Pregel(spGraph)(initialMessage)((v, msg) => addMaps(v.attr, msg))(sendMessage)(addMaps)
  }
}

object ShortestPathsExample extends App {

  // convert from an RDD of tuples to an edge RDD
  private def fromTuplesToEdges (edges: RDD[(VertexId, VertexId)]): EdgeRDD[Null] =
    map(edges)(map(_) { case (s, t) => Edge(s, t, null)})

  def run = {
    // an edge RDD with three partitions
    val edges: EdgeRDD[Null] = fromTuplesToEdges(List(
      List((1, 2), (3, 2), (4, 5), (6, 8)),
      List((5, 7), (8, 9), (10, 9), (9, 6)),
      List((9, 10))
    ))
    val vertices: VertexRDD[Null] = List(List.range(1, 11).map(Vertex(_, null)))
    val result = ShortestPaths.run(GraphRDD(vertices, edges), Seq(2, 7, 8, 10))

    println()
    println("Finding shortest paths to landmarks:")

    result.vertexRDD.flatten.foreach(println)
  }

  ShortestPathsExample.run
}