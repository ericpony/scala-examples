import leon.lang._
import scala.language.postfixOps

object ScalaMapSpec {
  def insert_commu_lemma[K, V] (map: Map[K, V], p1: (K, V), p2: (K, V)): Boolean = {
    require(p1._1 != p2._1)
    map + p1 + p2 == map + p2 + p1
  } holds /* verified */

  def merge_commu_lemma[K, V] (map1: Map[K, V], map2: Map[K, V], k: K): Boolean = {
    (map2 ++ map1).contains(k) == (map1 ++ map2).contains(k)
  } holds /* union operation cannot be translated */

  def merge_assoc_lemma[K, V] (map1: Map[K, V], map2: Map[K, V], map3: Map[K, V]): Boolean = {
    map1 ++ (map2 ++ map3) == (map1 ++ map2) ++ map3
  } holds /* union operation cannot be translated */
}
