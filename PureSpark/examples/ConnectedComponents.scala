package purespark.examples

import purespark.GraphX._
import purespark.Prelude._

/**
 * Connected components algorithm.
 */
object ConnectedComponents {
  /**
   * Compute the connected component membership of each vertex and return a graph with the vertex
   * value containing the lowest vertex id in the connected component containing that vertex.
   *
   * @tparam V the vertex attribute type (discarded in the computation)
   * @tparam E the edge attribute type (preserved in the computation)
   *
   * @param graph the graph for which to compute the connected components
   *
   * @return a graph with vertex attributes containing the smallest vertex in each
   *         connected component
   */
  def run[V, E] (graph: GraphRDD[V, _]): GraphRDD[VertexId, _] = {
    val ccGraph = GraphRDD(mapVertices[V, VertexId](graph.vertexRDD)(_.id), graph.edgeRDD)
    def sendMessage (edge: EdgeTriplet[VertexId, _]): List[Vertex[VertexId]] = {
      if (edge.srcAttr < edge.dstAttr) {
        List(Vertex(edge.dstId, edge.srcAttr))
      } else if (edge.srcAttr > edge.dstAttr) {
        List(Vertex(edge.srcId, edge.dstAttr))
      } else {
        List.empty
      }
    }
    Pregel(ccGraph)(Int.MaxValue)((v, msg) => scala.math.min(v.attr, msg))(sendMessage)((a, b) => scala.math.min(a, b))
  } // end of connectedComponents
}

object ConnectedComponentsExample extends App {

  // convert from an RDD of tuples to an edge RDD
  private def fromTuplesToEdges (edges: RDD[(VertexId, VertexId)]): EdgeRDD[Null] =
    map(edges)(map(_) { case (s, t) => Edge(s, t, null)})

  def run = {
    // an edge RDD with two partitions
    val edges: EdgeRDD[Null] = fromTuplesToEdges(List(
      List((1, 2), (3, 2), (4, 5), (6, 8)),
      List((5, 7), (8, 9), (10, 10), (9, 6))
    ))
    val vertices: VertexRDD[Null] = List(List.range(1, 11).map(Vertex(_, null)))
    val result = ConnectedComponents.run(GraphRDD(vertices, edges))

    println()
    println("Identifying connected components:")

    result.vertexRDD.flatten.foreach(println)
  }

  ConnectedComponentsExample.run
}