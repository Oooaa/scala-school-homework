package lectures.collections

import lectures.collections.CherryTree.{Node, Node1, Node2}

import scala.collection.generic._
import scala.collection.{GenTraversableOnce, LinearSeq, LinearSeqOptimized, mutable}

sealed trait CherryTree[+T] extends LinearSeq[T]
  with LinearSeqOptimized[T, CherryTree[T]]
  with GenericTraversableTemplate[T, CherryTree]
  with Product with Serializable {
  override def init: CherryTree[T]

  override def last: T

  def append[S >: T](x: S): CherryTree[S]

  def prepend[S >: T](x: S): CherryTree[S]

  def concat[S >: T](xs: CherryTree[S]): CherryTree[S]

  override def toString(): String = super.toString()

  override def companion = CherryTree

  override def stringPrefix: String = "CherryTree"


  // If we have a default builder, there are faster ways to perform some operations
  @inline private[this] def isDefaultCBF[A, B, That](bf: CanBuildFrom[CherryTree[A], B, That]): Boolean = bf eq CherryTree.ReusableCBF

  override def :+[B >: T, That](elem: B)(implicit bf: CanBuildFrom[CherryTree[T], B, That]) =
    if (isDefaultCBF(bf)) append(elem).asInstanceOf[That] else super.:+(elem)

  override def +:[B >: T, That](elem: B)(implicit bf: CanBuildFrom[CherryTree[T], B, That]) =
    if (isDefaultCBF(bf)) prepend(elem).asInstanceOf[That] else super.:+(elem)

  override def ++[B >: T, That](that: GenTraversableOnce[B])(implicit bf: CanBuildFrom[CherryTree[T], B, That]) =
    if (isDefaultCBF(bf)) concat(that.asInstanceOf[CherryTree[B]]).asInstanceOf[That] else super.++(that)
}

case object CherryNil extends CherryTree[Nothing] {
  override def head = throw new NoSuchElementException("head of empty CherryList")

  override def tail = throw new UnsupportedOperationException("tail of empty CherryList")

  override def init = throw new UnsupportedOperationException("init of empty CherryList")

  override def last = throw new NoSuchElementException("last of empty CherryList")

  override def foreach[U](f: (Nothing) => U) = ()

  override def append[S >: Nothing](x: S): CherryTree[S] = CherrySingle(x)

  override def size = 0

  override def isEmpty = true

  override def prepend[S >: Nothing](x: S) = append(x)

  override def concat[S >: Nothing](xs: CherryTree[S]) = xs
}

final case class CherrySingle[+T](x: T) extends CherryTree[T] {
  override def head = x

  override def tail = CherryNil

  override def foreach[U](f: T => U) = f(x)

  def append[S >: T](y: S) = CherryBranch(Node1(x), CherryNil, Node1(y))

  override def size = 1

  override def isEmpty = false

  override def prepend[S >: T](y: S) = CherryBranch(Node1(y), CherryNil, Node1(x))

  override def concat[S >: T](xs: CherryTree[S]) = xs.prepend(x)
}

final case class CherryBranch[+T](left: Node[T], inner: CherryTree[Node2[T]], right: Node[T]) extends CherryTree[T] {
  override def head = left match {
    case Node1(x) => x
    case Node2(x, _) => x
  }

  override def tail = left match {
    case Node1(_) => inner match {
      case CherryNil => right match {
        case Node1(x) => CherrySingle(x)
        case Node2(x, y) => CherryBranch(Node1(x), CherryNil, Node1(y))
      }
      case tree => CherryBranch(tree.head, tree.tail, right)
    }
    case Node2(_, x) => CherryBranch(Node1(x), inner, right)
  }

  override def foreach[U](f: T => U) = {
    left.foreach(f)
    inner.foreach(_.foreach(f))
    right.foreach(f)
  }

  def append[S >: T](x: S) = right match {
    case Node1(y) => CherryBranch(left, inner, Node2(y, x))
    case n: Node2[S] => CherryBranch(left, inner.append(n), Node1(x))
  }

  override def size = left.size + inner.size * 2 + right.size

  override def isEmpty = false

  override def prepend[S >: T](x: S) =
    left match {
      case Node1(y) => CherryBranch(Node2(x, y), inner, right)
      case node: Node2[S] => CherryBranch(Node1(x), inner.prepend(node), right)
    }

  override def concat[S >: T](xs: CherryTree[S]) =
    this.foldRight(xs)((el: T, tree: CherryTree[S]) => tree.prepend(el))

  override def apply(n: Int): T =
    n match {
      case z if z < 0 || z >= size => throw new IndexOutOfBoundsException("This index is not within possible bounds")
      case z if left.size > z =>
        left match {
          case Node1(_) => _
          case Node2(a, b) => if (z == 0) a else b
        }
      case z if z < size - right.size =>
        val nodeIndex = (z - left.size) / 2
        val tmpNode = inner.apply(nodeIndex)
        if ((z - left.size) % 2 == 0) tmpNode.x
        else tmpNode.y
      case z =>
        right match {
          case Node1(_) => _
          case Node2(a, b) => if (z == size - 1) b else a
        }

    }
}


object CherryTree extends SeqFactory[CherryTree] {

  private class CherryTreeBuilder[T]() extends mutable.Builder[T, CherryTree[T]] {
    private[this] var coll: CherryTree[T] = CherryNil

    def +=(elem: T) = {
      coll = coll.append(elem);
      this
    }

    def clear(): Unit = coll = CherryNil

    def result(): CherryTree[T] = coll
  }

  implicit def canBuildFrom[A]: CanBuildFrom[Coll, A, CherryTree[A]] =
    ReusableCBF.asInstanceOf[GenericCanBuildFrom[A]]

  def newBuilder[T]: mutable.Builder[T, CherryTree[T]] = new CherryTreeBuilder[T]

  sealed trait Node[+T] {
    def foreach[U](f: T => U): Unit

    def size: Int
  }

  final case class Node1[+T](x: T) extends Node[T] {
    override def foreach[U](f: (T) => U): Unit = f(x)

    def size = 1
  }

  final case class Node2[+T](x: T, y: T) extends Node[T] {
    def foreach[U](f: (T) => U): Unit = {
      f(x)
      f(y)
    }

    def size = 2
  }

}

