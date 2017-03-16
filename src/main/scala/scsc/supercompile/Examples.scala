package scsc.supercompile

object Examples {
  // 3
  val length1 = """
  letrec length = (\xs -> case xs of Nil -> 0 | (Cons x xs) -> 1 + (length xs)) in length (Cons 7 (Cons 8 (Cons 9 Nil)))
  """

  // 0
  val length2 = """
  letrec length = (\xs -> case xs of Nil -> 0 | (Cons x xs) -> 1 + (length xs)) in length Nil
  """

  // Nil
  val append1 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons x xs) -> (Cons x (append xs ys))) in (append Nil Nil)
  """

  // (Cons 1 (Cons 2 Nil))
  val append2 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons x xs) -> (Cons x (append xs ys))) in (append (Cons 1 Nil) (Cons 2 Nil))
  """

  // [[(letrec ys = (Cons x Nil) in (Cons 1 ys))]]
  val append3 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons x xs) -> (Cons x (append xs ys))) in (append (Cons 1 Nil) (Cons x Nil))
  """

  // [[(let ys = (Cons x Nil) in (Cons y ys))]]
  val append4 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons x xs) -> (Cons x (append xs ys))) in (append (Cons y Nil) (Cons x Nil))
  """

  // does not terminate
  val append5 = """
  letrec append = (\xs -> \ys -> case xs of Nil -> ys | (Cons x xs) -> (Cons x (append xs ys))) in (append (append xs ys) zs)
  """

  // [[(a * a * a)]]
  val pow1 = """
  letrec pow = (\x -> \n -> case n of 0 -> 1 | n -> (pow x (n-1)) * x) in (pow a 3)
  """

  // does not terminate
  val pow2 = """
  letrec pow = (\x -> \n -> case n of 0 -> 1 | n -> (pow x (n-1)) * x) in (pow 2 a)
  """

  // [[(let r = (a * (let r = (let r = a in (r * r)) in (r * r))) in (r * r))]]
  val logpow1 = """
  letrec even = (\n -> case n of 0 -> True | 1 -> False | n -> (even (n-2))) in (letrec pow = (\x -> (\n -> case n of 0 -> 1 | n -> case (n % 2) of 0 -> (let r = (pow x (n / 2)) in (r*r)) | 1 -> x * (pow x (n-1)))) in (pow a 10))
  """

}
