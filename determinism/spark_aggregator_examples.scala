// https://github.com/chaordic/ignition-core/blob/master/src/main/scala/ignition/core/jobs/utils/RDDUtils.scala
def groupByKeyAndTake(n: Int): RDD[(K, List[V])] = {
    rdd.aggregateByKey(List.empty[V])(
        (lst, v) => 
          if (lst.size >= n) lst
          else v :: lst
        (lstA, lstB) =>
          if (lstA.size >= n) lstA
          else if (lstB.size >= n) lstB
          else {
            if (lstA.size + lstB.size > n) {
              (lstA ++ lstB).take(n)
            } else
              lstA ++ lstB
          }
    )
}
// same as above
def groupByKeyAndTakeOrdered[B >: V](n: Int)(implicit ord: Ordering[B]): RDD[(K, List[V])] = {
  rdd.aggregateByKey(List.empty[V])(
    (lst, v) => (v :: lst).sorted(ord).take(n),
    (lstA, lstB) => (lstA ++ lstB).sorted(ord).take(n))
}

// https://github.com/apache/spark/blob/master/mllib/src/main/scala/org/apache/spark/mllib/stat/MultivariateOnlineSummarizer.scala
// Caution: Double type
val featureSummary = features.aggregate(new MultivariateOnlineSummarizer())(
  (summary, feat) => summary.add(feat),
  (sum1, sum2) => sum1.merge(sum2))
  
// https://github.com/apache/spark/blob/master/core/src/main/scala/org/apache/spark/rdd/RDD.scala
// https://github.com/addthis/stream-lib/blob/master/src/main/java/com/clearspring/analytics/stream/cardinality/HyperLogLogPlus.java
def countApproxDistinct(p: Int, sp: Int): Long = withScope {
    val zeroCounter = new HyperLogLogPlus(p, sp)
    aggregate(zeroCounter)(
      (hll: HyperLogLogPlus, v: T) => {
        hll.offer(v)
        hll
      },
      (h1: HyperLogLogPlus, h2: HyperLogLogPlus) => {
        h1.addAll(h2)
        h1
      }).cardinality()
}

// https://github.com/SleepyThread/spark/blob/master/mllib/src/main/scala/org/apache/spark/mllib/rdd/MLPairRDDFunctions.scala
def topByKey(num: Int)(implicit ord: Ordering[V]): RDD[(K, Array[V])] = {
    self.aggregateByKey(new BoundedPriorityQueue[V](num)(ord))(
      seqOp = (queue, item) => {
        queue += item
      },
      combOp = (queue1, queue2) => {
        queue1 ++= queue2
      }
    ).mapValues(_.toArray.sorted(ord.reverse))  // This is an min-heap, so we reverse the order.

}

// https://github.com/tomwhite/hadoop-book/blob/master/ch19-spark/src/test/scala/TransformationsAndActionsTest.scala
val sets: RDD[(String, HashSet[Int])] = 
  pairs.aggregateByKey(new HashSet[Int])(_+=_, _++=_)

// https://github.com/javadba/sparkperf/blob/master/src/main/scala/com/blazedb/sparkperf/CoreBattery.scala
val countRdds = Seq(
  (s"$testName AggregateByKey", inputRdd.aggregateByKey(0L)((k, v) => k * v.length, (k, v) => k + v))
)

rdd.aggregate((0,0)) (
  (x,y) => (x._1 + y, x._2 + 1),
  (x,y) => (x._1 + y._1, x._2 + y._2))

// https://github.com/apache/spark/blob/master/sql/core/src/main/scala/org/apache/spark/sql/execution/stat/FrequentItems.scala
val countMaps = Seq.tabulate(numCols)(i => new FreqItemCounter(sizeOfMap))
val freqItems = ...rdd.aggregate(countMaps)(
  seqOp = (counts, row) => {
    var i = 0
    while (i < numCols) {
      val thisMap = counts(i)
      val key = row.get(i)
      thisMap.add(key, 1L)
      i += 1
    }
    counts
  },
  combOp = (baseCounts, counts) => {
    var i = 0
    while (i < numCols) {
      baseCounts(i).merge(counts(i))
      i += 1
    }
    baseCounts
  }
)

// https://github.com/apache/spark/blob/master/mllib/src/main/scala/org/apache/spark/mllib/stat/KernelDensity.scala
val (densities, count) = sample.aggregate((new Array[Double](n), 0L))(
  (x, y) => {
    var i = 0
    while (i < n) {
      x._1(i) += normPdf(y, bandwidth, logStandardDeviationPlusHalfLog2Pi, points(i))
      i += 1
    }
    (x._1, x._2 + 1)
  },
  (x, y) => {
    blas.daxpy(n, 1.0, y._1, 1, x._1, 1)
    (x._1, x._2 + y._2)
  })

// https://github.com/apache/spark/blob/master/mllib/src/main/scala/org/apache/spark/mllib/clustering/GaussianMixture.scala
val sums = breezeData.aggregate(ExpectationSum.zero(k, d))(compute.value, _ += _)

// https://github.com/apache/spark/blob/master/mllib/src/main/scala/org/apache/spark/ml/feature/OneHotEncoder.scala
val numAttrs = rdd.aggregate(0.0)(
      (m, x) => math.max(m, x),
      (m0, m1) => math.max(m0, m1)
    ).toInt + 1

// https://github.com/apache/spark/blob/master/sql/core/src/main/scala/org/apache/spark/sql/execution/datasources/json/InferSchema.scala    
def compatibleRootType: (DataType, DataType) => DataType = {
    case (ArrayType(ty1, _), ty2) => compatibleRootType(ty1, ty2)
    case (ty1, ArrayType(ty2, _)) => compatibleRootType(ty1, ty2)
    case (ty1, ty2) => compatibleType(ty1, ty2)
}        
rdd.treeAggregate(StructType(Seq()))(compatibleRootType, compatibleRootType)

// https://github.com/apache/spark/blob/master/sql/core/src/main/scala/org/apache/spark/sql/execution/stat/StatFunctions.scala
// Caution: Double type
rdd.aggregate(new CovarianceCounter)(
  seqOp = (counter, row) => {
    counter.add(row.getDouble(0), row.getDouble(1))
  },
  combOp = (baseCounter, other) => {
    baseCounter.merge(other)
})

pairedRDD.map {
  case (key, row) =>
    mapAll(key, row)
}.aggregateByKey[Seq[Any]](zeroValues, numPartitions)(
  (aggregateValues, columnValues) => addAll(aggregateValues, columnValues),
  (aggregateValues1, aggregateValues2) => mergeAll(aggregateValues1, aggregateValues2)
)

// https://github.com/apache/spark/blob/master/mllib/src/main/scala/org/apache/spark/mllib/linalg/distributed/RowMatrix.scala
// Caution: Double type
rows.treeAggregate(BDV.zeros[Double](n))(
  seqOp = (U, r) => {
    val rBrz = r.toBreeze
    val a = rBrz.dot(vbr.value)
    rBrz match {
      // use specialized axpy for better performance
      case _: BDV[_] => brzAxpy(a, rBrz.asInstanceOf[BDV[Double]], U)
      case _: BSV[_] => brzAxpy(a, rBrz.asInstanceOf[BSV[Double]], U)
      case _ => throw new UnsupportedOperationException
    }
    U
  }, combOp = (U1, U2) => U1 += U2)
  
val summary = rows.treeAggregate(new MultivariateOnlineSummarizer)(
  (aggregator, data) => aggregator.add(data),
  (aggregator1, aggregator2) => aggregator1.merge(aggregator2))
  
val GU = rows.treeAggregate(new BDV[Double](new Array[Double](nt)))(
  seqOp = (U, v) => {
    RowMatrix.dspr(1.0, v, U.data)
    U
  }, combOp = (U1, U2) => U1 += U2)
  
val (m, mean) = rows.treeAggregate[(Long, BDV[Double])]((0L, BDV.zeros[Double](n)))(
  seqOp = (s: (Long, BDV[Double]), v: Vector) => (s._1 + 1L, s._2 += v.toBreeze),
  combOp = (s1: (Long, BDV[Double]), s2: (Long, BDV[Double])) =>
    (s1._1 + s2._1, s1._2 += s2._2)
)

// https://github.com/apache/spark/blob/master/mllib/src/main/scala/org/apache/spark/mllib/feature/IDF.scala
val idf = dataset.treeAggregate(new IDF.DocumentFrequencyAggregator(minDocFreq = minDocFreq))(
  seqOp = (df, v) => df.add(v),
  combOp = (df1, df2) => df1.merge(df2)
).idf()

// https://github.com/apache/spark/blob/master/core/src/main/scala/org/apache/spark/util/random/StratifiedSamplingUtils.scala
def getAcceptanceResults[K, V](rdd: RDD[(K, V)],
  withReplacement: Boolean,
  fractions: Map[K, Double],
  counts: Option[Map[K, Long]],
  seed: Long): mutable.Map[K, AcceptanceResult] = {
    val combOp = getCombOp[K]
    val mappedPartitionRDD = rdd.mapPartitionsWithIndex { case (partition, iter) =>
      val zeroU: mutable.Map[K, AcceptanceResult] = new mutable.HashMap[K, AcceptanceResult]()
      val rng = new RandomDataGenerator()
      rng.reSeed(seed + partition)
      val seqOp = getSeqOp(withReplacement, fractions, rng, counts)
      Iterator(iter.aggregate(zeroU)(seqOp, combOp))
    }
    mappedPartitionRDD.reduce(combOp)
}

// https://github.com/apache/spark/blob/master/core/src/test/scala/org/apache/spark/rdd/RDDSuite.scala
val pairs = sc.makeRDD(Array(("a", 1), ("b", 2), ("a", 2), ("c", 5), ("a", 3)))
type StringMap = HashMap[String, Int]
val emptyMap = new StringMap {
  override def default(key: String): Int = 0
}
val mergeElement: (StringMap, (String, Int)) => StringMap = (map, pair) => {
  map(pair._1) += pair._2
  map
}
val mergeMaps: (StringMap, StringMap) => StringMap = (map1, map2) => {
  for ((key, value) <- map2) {
    map1(key) += value
  }
  map1
}
val result = pairs.aggregate(emptyMap)(mergeElement, mergeMaps)
assert(result.toSet === Set(("a", 6), ("b", 2), ("c", 5)))

// https://github.com/apache/spark/blob/master/mllib/src/main/scala/org/apache/spark/mllib/optimization/LBFGS.scala
val (gradientSum, lossSum) = data.treeAggregate((Vectors.zeros(n), 0.0))(
  seqOp = (c, v) => (c, v) match { case ((grad, loss), (label, features)) =>
    val l = localGradient.compute(
      features, label, bcW.value, grad)
    (grad, loss + l)
  },
  combOp = (c1, c2) => (c1, c2) match { case ((grad1, loss1), (grad2, loss2)) =>
    axpy(1.0, grad2, grad1)
    (grad1, loss1 + loss2)
  })
  
// https://github.com/apache/spark/blob/master/mllib/src/main/scala/org/apache/spark/mllib/recommendation/MatrixFactorizationModel.scala  
def countApproxDistinctUserProduct(usersProducts: RDD[(Int, Int)]): (Long, Long) = {
    val zeroCounterUser = new HyperLogLogPlus(4, 0)
    val zeroCounterProduct = new HyperLogLogPlus(4, 0)
    val aggregated = usersProducts.aggregate((zeroCounterUser, zeroCounterProduct))(
      (hllTuple: (HyperLogLogPlus, HyperLogLogPlus), v: (Int, Int)) => {
        hllTuple._1.offer(v._1)
        hllTuple._2.offer(v._2)
        hllTuple
      },
      (h1: (HyperLogLogPlus, HyperLogLogPlus), h2: (HyperLogLogPlus, HyperLogLogPlus)) => {
        h1._1.addAll(h2._1)
        h1._2.addAll(h2._2)
        h1
      })
    (aggregated._1.cardinality(), aggregated._2.cardinality())
}

// https://github.com/apache/spark/blob/master/mllib/src/main/scala/org/apache/spark/ml/recommendation/ALS.scala
ratings.map { r =>
   ((srcPart.getPartition(r.user), dstPart.getPartition(r.item)), r)
 }.aggregateByKey(new RatingBlockBuilder)(
     seqOp = (b, r) => b.add(r),
     combOp = (b0, b1) => b0.merge(b1.build()))
   .mapValues(_.build())
   
def computeYtY(factorBlocks: RDD[(Int, FactorBlock)], rank: Int): NormalEquation = {
    factorBlocks.values.aggregate(new NormalEquation(rank))(
      seqOp = (ne, factors) => {
        factors.foreach(ne.add(_, 0.0))
        ne
      },
      combOp = (ne1, ne2) => ne1.merge(ne2))
}

// https://github.com/apache/spark/blob/master/mllib/src/test/scala/org/apache/spark/ml/classification/LogisticRegressionSuite.scala
val histogram = binaryDataset.map { case Row(label: Double, features: Vector) => label }
  .treeAggregate(new MultiClassSummarizer)(
    seqOp = (c, v) => (c, v) match {
      case (classSummarizer: MultiClassSummarizer, label: Double) => classSummarizer.add(label)
    },
    combOp = (c1, c2) => (c1, c2) match {
      case (classSummarizer1: MultiClassSummarizer, classSummarizer2: MultiClassSummarizer) =>
        classSummarizer1.merge(classSummarizer2)
    }).histogram
   
// https://github.com/apache/spark/blob/master/mllib/src/main/scala/org/apache/spark/mllib/clustering/KMeans.scala    
val sumCosts = costs
    .aggregate(Vectors.zeros(runs))(
      seqOp = (s, v) => {
        // s += v
        axpy(1.0, v, s)
        s
      },
      combOp = (s0, s1) => {
        // s0 += s1
        axpy(1.0, s1, s0)
        s0
      })

// https://github.com/apache/spark/blob/master/mllib/src/test/scala/org/apache/spark/mllib/feature/StandardScalerSuite.scala    
def computeSummary(data: RDD[Vector]): MultivariateStatisticalSummary = {
    data.treeAggregate(new MultivariateOnlineSummarizer)(
        (aggregator, data) => aggregator.add(data),
        (aggregator1, aggregator2) => aggregator1.merge(aggregator2))
}
